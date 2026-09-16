import SixVertexUnfolding.Geometry.ShortestHingeStraightness
import SixVertexUnfolding.Geometry.NonvertexFacetNeighborhoods

/-! Local straight developments of actual shortest surface paths. The central
point may lie in a facet or in an original edge; only original vertices are excluded. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SurfacePath

open Set Filter
open scoped Topology

variable {P : ConvexPolyhedron} {a b : Space}

/-- A neighborhood of an interior path parameter contains a smaller closed interval. -/
theorem interval_inside_neighborhood (path : P.SurfacePath a b) (m : unitInterval)
    (after_start : 0 < m) (before_end : m < 1) (U : Set Space)
    (openU : IsOpen U) (at_center : path.curve m ∈ U) :
    ∃ s t : unitInterval, s < m ∧ m < t ∧ ∀ u ∈ Icc s t, path.curve u ∈ U := by
  have near : path.curve ⁻¹' U ∈ 𝓝 m :=
    path.curve.continuous.continuousAt.preimage_mem_nhds (openU.mem_nhds at_center)
  obtain ⟨l, r, bounds, contained⟩ :=
    (mem_nhds_iff_exists_Ioo_subset' ⟨0, after_start⟩ ⟨1, before_end⟩).mp near
  obtain ⟨s, ls, sm⟩ := exists_between bounds.1
  obtain ⟨t, mt, tr⟩ := exists_between bounds.2
  exact ⟨s, t, sm, mt, fun u hu => contained ⟨ls.trans_le hu.1, hu.2.trans_lt tr⟩⟩

/-- A short portion has two rigid face placements that agree at the crossing,
and both of its developed pieces lie on one straight segment. -/
structure LocalStraightDevelopment (path : P.SurfacePath a b) (m : unitInterval) where
  start : unitInterval
  finish : unitInterval
  before : start < m
  after : m < finish
  first : P.Face
  second : P.Face
  first_piece : ∀ u ∈ Icc start m, path.curve u ∈ first.val
  second_piece : ∀ u ∈ Icc m finish, path.curve u ∈ second.val
  incident : first = second ∨ P.ShareEdge first second
  left : Space →ᵃ[ℝ] Plane
  right : Space →ᵃ[ℝ] Plane
  left_rigid : ∀ x ∈ first.val, ∀ y ∈ first.val, dist (left x) (left y) = dist x y
  right_rigid : ∀ x ∈ second.val, ∀ y ∈ second.val, dist (right x) (right y) = dist x y
  joined : Set.EqOn left right (first.val ∩ second.val)
  first_straight : ∀ u ∈ Icc start m,
    left (path.curve u) ∈ segment ℝ (left (path.curve start)) (right (path.curve finish))
  second_straight : ∀ u ∈ Icc m finish,
    right (path.curve u) ∈ segment ℝ (left (path.curve start)) (right (path.curve finish))

/-- Straightness of the central crossing controls the entire two-face portion. -/
theorem two_face_development_of_between (path : P.SurfacePath a b)
    (shortest : path.IsShortest) (finite : path.length ≠ ⊤)
    (s m t : unitInterval) (sm : s < m) (mt : m < t) (F G : P.Face)
    (hs : path.curve s ∈ F.val) (hm : path.curve m ∈ F.val ∩ G.val) (ht : path.curve t ∈ G.val)
    (incident : F = G ∨ P.ShareEdge F G) (left right : Space →ᵃ[ℝ] Plane)
    (left_rigid : ∀ x ∈ F.val, ∀ y ∈ F.val, dist (left x) (left y) = dist x y)
    (right_rigid : ∀ x ∈ G.val, ∀ y ∈ G.val, dist (right x) (right y) = dist x y)
    (joined : Set.EqOn left right (F.val ∩ G.val))
    (between : Wbtw ℝ (left (path.curve s)) (left (path.curve m)) (right (path.curve t))) :
    Nonempty (LocalStraightDevelopment path m) := by
  have first_range := path.shortest_portion_range shortest finite F s m sm.le hs hm.1
  have second_range := path.shortest_portion_range shortest finite G m t mt.le hm.2 ht
  refine ⟨{
    start := s, finish := t, before := sm, after := mt, first := F, second := G
    first_piece := fun u hu => F.convex.segment_subset hs hm.1 (first_range u hu)
    second_piece := fun u hu => G.convex.segment_subset hm.2 ht (second_range u hu)
    incident := incident, left := left, right := right
    left_rigid := left_rigid, right_rigid := right_rigid, joined := joined
    first_straight := ?_, second_straight := ?_ }⟩
  · intro u hu
    apply (convex_segment (left (path.curve s)) (right (path.curve t))).segment_subset
      (left_mem_segment ℝ _ _) between.mem_segment
    rw [← image_segment ℝ left]
    exact ⟨path.curve u, first_range u hu, rfl⟩
  · intro u hu
    apply (convex_segment (left (path.curve s)) (right (path.curve t))).segment_subset
      between.mem_segment (right_mem_segment ℝ _ _)
    rw [joined hm, ← image_segment ℝ right]
    exact ⟨path.curve u, second_range u hu, rfl⟩

/-- Every nonvertex interior point of a finite shortest path has a straight local development. -/
theorem exists_local_straight_development (path : P.SurfacePath a b)
    (shortest : path.IsShortest) (finite : path.length ≠ ⊤)
    (m : unitInterval) (after_start : 0 < m) (before_end : m < 1)
    (not_vertex : path.curve m ∉ P.vertices) : Nonempty (LocalStraightDevelopment path m) := by
  obtain ⟨U, openU, center, incident⟩ := P.incident_facets_neighborhood (path.curve m)
  obtain ⟨s, t, sm, mt, near⟩ := path.interval_inside_neighborhood m after_start before_end U openU center
  obtain ⟨F, hs⟩ := P.boundary_point_in_face (path.on_surface s)
  obtain ⟨G, ht⟩ := P.boundary_point_in_face (path.on_surface t)
  have hm : path.curve m ∈ F.val ∩ G.val :=
    ⟨incident _ (near s ⟨le_rfl, sm.le.trans mt.le⟩) F hs,
      incident _ (near t ⟨sm.le.trans mt.le, le_rfl⟩) G ht⟩
  by_cases same : F = G
  · subst G
    obtain ⟨place, rigid⟩ := F.exists_rigid_placement
    apply path.two_face_development_of_between shortest finite s m t sm mt F F hs hm ht
      (Or.inl rfl) place place rigid rigid (fun _ _ => rfl)
    apply mem_segment_iff_wbtw.mp
    rw [← image_segment ℝ place]
    exact ⟨path.curve m, path.shortest_portion_range shortest finite F s t (sm.le.trans mt.le)
      hs ht m ⟨sm.le, mt.le⟩, rfl⟩
  · have shared := F.shareEdge_of_common_nonvertex G same hm not_vertex
    obtain ⟨left, right, left_rigid, right_rigid, joined, _, between⟩ :=
      path.exists_straight_two_face_development shortest finite F G shared s m t sm.le mt.le hs hm ht not_vertex
    exact path.two_face_development_of_between shortest finite s m t sm mt F G hs hm ht
      (Or.inr shared) left right left_rigid right_rigid joined between

end SixVertexUnfolding.ConvexPolyhedron.SurfacePath
