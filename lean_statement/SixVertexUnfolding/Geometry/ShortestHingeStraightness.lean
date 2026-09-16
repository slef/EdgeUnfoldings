import SixVertexUnfolding.Geometry.ShortestHingeVariation
import SixVertexUnfolding.Geometry.UnfoldedHingeDirections
import SixVertexUnfolding.Geometry.PolygonPetal

/-! Shortest paths cross an original edge in a straight line when its two
incident facets are unfolded outward. This is proved for actual surface paths. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SurfacePath

open Set
open scoped ENNReal NNReal

variable {P : ConvexPolyhedron} {a b : Space}

/-- In any outward rigid placement of two facets, a shortest edge crossing is straight. -/
theorem shortest_crossing_unfolds_straight (path : P.SurfacePath a b) (shortest : path.IsShortest)
    (finite : path.length ≠ ⊤) (F G : P.Face) (s m t : unitInterval)
    (sm : s ≤ m) (mt : m ≤ t) (hs : path.curve s ∈ F.val)
    (hm : path.curve m ∈ F.val ∩ G.val) (ht : path.curve t ∈ G.val)
    (p q : Space) (pq : p ≠ q) (hp : p ∈ F.val ∩ G.val) (hq : q ∈ F.val ∩ G.val)
    (inside_edge : path.curve m ∈ openSegment ℝ p q)
    (left right : Space →ᵃ[ℝ] Plane)
    (left_rigid : ∀ x ∈ F.val, ∀ y ∈ F.val, dist (left x) (left y) = dist x y)
    (right_rigid : ∀ x ∈ G.val, ∀ y ∈ G.val, dist (right x) (right y) = dist x y)
    (joined : Set.EqOn left right (F.val ∩ G.val))
    (outward : OppositeHingeSides (left p) (left q) (left (path.curve s)) (right (path.curve t))) :
    Wbtw ℝ (left (path.curve s)) (left (path.curve m)) (right (path.curve t)) := by
  by_cases same_left : path.curve s = path.curve m
  · rw [same_left]
    exact ⟨0, by norm_num, by simp⟩
  by_cases same_right : path.curve t = path.curve m
  · rw [same_right, ← joined hm]
    exact ⟨1, by norm_num, by simp⟩
  have hinge_distinct : left p ≠ left q := by
    intro same
    exact pq (dist_eq_zero.mp (by simpa [same] using (left_rigid p hp.1 q hq.1).symm))
  have xz : left (path.curve s) ≠ left (path.curve m) := by
    intro same
    exact same_left (dist_eq_zero.mp (by simpa [same] using (left_rigid _ hs _ hm.1).symm))
  have yz : right (path.curve t) ≠ left (path.curve m) := by
    rw [joined hm]
    intro same
    exact same_right (dist_eq_zero.mp (by simpa [same] using (right_rigid _ ht _ hm.2).symm))
  have line : left (path.curve m) ∈ affineSpan ℝ ({left p, left q} : Set Plane) := by
    apply convexHull_subset_affineSpan
    rw [convexHull_pair, ← image_segment ℝ left p q]
    exact ⟨path.curve m, openSegment_subset_segment ℝ p q inside_edge, rfl⟩
  apply unfolded_stationary_hinge_is_straight p q (path.curve m) (path.curve s) (path.curve t)
    (left p) (left q) (left (path.curve m)) (left (path.curve s)) (right (path.curve t))
    hinge_distinct xz yz line (left_rigid _ hp.1 _ hq.1)
    (left_rigid _ hp.1 _ hs) (left_rigid _ hq.1 _ hs)
    (by rw [joined hp]; exact right_rigid _ hp.2 _ ht)
    (by rw [joined hq]; exact right_rigid _ hq.2 _ ht)
    (left_rigid _ hp.1 _ hm.1) (left_rigid _ hq.1 _ hm.1)
    (left_rigid _ hs _ hm.1)
    (by rw [joined hm]; exact right_rigid _ ht _ hm.2)
    (path.shortest_hinge_stationary shortest finite F G s m t sm mt hs hm ht
      same_left same_right p q hp hq inside_edge) outward

/-- The required outward placements exist, so straightness is not conditional on a missing chart. -/
theorem exists_straight_two_face_development (path : P.SurfacePath a b) (shortest : path.IsShortest)
    (finite : path.length ≠ ⊤) (F G : P.Face) (shared : P.ShareEdge F G)
    (s m t : unitInterval) (sm : s ≤ m) (mt : m ≤ t)
    (hs : path.curve s ∈ F.val) (hm : path.curve m ∈ F.val ∩ G.val) (ht : path.curve t ∈ G.val)
    (not_vertex : path.curve m ∉ P.vertices) :
    ∃ left right : Space →ᵃ[ℝ] Plane,
      (∀ x ∈ F.val, ∀ y ∈ F.val, dist (left x) (left y) = dist x y) ∧
      (∀ x ∈ G.val, ∀ y ∈ G.val, dist (right x) (right y) = dist x y) ∧
      Set.EqOn left right (F.val ∩ G.val) ∧
      Disjoint (interior (left '' F.val)) (interior (right '' G.val)) ∧
      Wbtw ℝ (left (path.curve s)) (left (path.curve m)) (right (path.curve t)) := by
  obtain ⟨p, p_vertex, q, q_vertex, pq, edge⟩ := F.shared_edge_endpoints G shared
  have hp : p ∈ F.val ∩ G.val := edge ▸ left_mem_segment ℝ p q
  have hq : q ∈ F.val ∩ G.val := edge ▸ right_mem_segment ℝ p q
  have inside : path.curve m ∈ openSegment ℝ p q :=
    mem_openSegment_of_ne_left_right (fun equal => not_vertex (equal ▸ p_vertex))
      (fun equal => not_vertex (equal ▸ q_vertex)) (edge ▸ hm)
  obtain ⟨left, left_rigid⟩ := F.exists_rigid_placement
  obtain ⟨right, right_rigid, joined, safe, _, outward⟩ := F.exists_polygon_petal G shared left left_rigid
  exact ⟨left, right, left_rigid, right_rigid, joined, safe,
    path.shortest_crossing_unfolds_straight shortest finite F G s m t sm mt hs hm ht
      p q pq hp hq inside left right left_rigid right_rigid joined
      (outward p ⟨hp, p_vertex⟩ q ⟨hq, q_vertex⟩ pq _ hs _ ht)⟩

end SixVertexUnfolding.ConvexPolyhedron.SurfacePath
