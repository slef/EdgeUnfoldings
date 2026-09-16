import SixVertexUnfolding.Geometry.SurfaceTopology
import SixVertexUnfolding.Geometry.FacetVertices
import SixVertexUnfolding.Geometry.TreeDevelopment

/-!
Removing the original vertices leaves a connected surface. Two distinct facets
that meet on this punctured surface share an edge. Consequently the facet dual
graph is connected and has a spanning tree of original hinges.
-/

namespace SixVertexUnfolding.ConvexPolyhedron

namespace Face

variable {P : ConvexPolyhedron} (F G : P.Face)

/-- Distinct facets meeting anywhere other than an original vertex share an original edge. -/
theorem shareEdge_of_common_nonvertex (distinct : F ≠ G) {x : Space}
    (common : x ∈ F.val ∩ G.val) (not_vertex : x ∉ P.vertices) : P.ShareEdge F G := by
  have upper := F.intersection_dimension_le_one G distinct
  by_contra not_edge
  have dimension_zero : affineDimension (F.val ∩ G.val) = 0 := by
    change affineDimension (F.val ∩ G.val) ≠ 1 at not_edge
    omega
  change Module.finrank ℝ (affineSpan ℝ (F.val ∩ G.val)).direction = 0 at dimension_zero
  rw [direction_affineSpan] at dimension_zero
  have subsingleton : (F.val ∩ G.val).Subsingleton :=
    (vectorSpan_eq_bot_iff_subsingleton ℝ).mp (Submodule.finrank_eq_zero.mp dimension_zero)
  have hull_nonempty : (convexHull ℝ ((F.val ∩ G.val) ∩ (P.vertices : Set Space))).Nonempty := by
    rw [← F.intersection_eq_convexHull_vertices G]
    exact ⟨x, common⟩
  obtain ⟨v, shared, vertex⟩ := convexHull_nonempty_iff.mp hull_nonempty
  exact not_vertex ((subsingleton shared common) ▸ vertex)

/-- Every facet has points other than the original vertices. -/
theorem nonvertex_nonempty : (F.val \ (P.vertices : Set Space)).Nonempty := by
  have finite_vertices := P.vertices.finite_toSet.subset
    (Set.inter_subset_right : F.val ∩ (P.vertices : Set Space) ⊆ (P.vertices : Set Space))
  obtain ⟨a, ha, b, hb, distinct⟩ := (Set.one_lt_ncard finite_vertices).mp
    (show 1 < (F.val ∩ (P.vertices : Set Space)).ncard by have := F.three_le_vertex_count; omega)
  let middle := midpoint ℝ a b
  have middle_in := F.convex.midpoint_mem ha.1 hb.1
  refine ⟨middle, middle_in, ?_⟩
  intro vertex
  rcases P.vertex_in_segment_is_endpoint vertex (F.subset_body ha.1) (F.subset_body hb.1)
    (midpoint_mem_segment (𝕜 := ℝ) a b) with left | right
  · exact distinct ((left_eq_midpoint_iff ℝ).mp left)
  · exact distinct ((right_eq_midpoint_iff ℝ).mp right)

end Face

/-- The graph whose vertices are facets and whose edges are shared original edges is connected. -/
theorem dualGraph_connected (P : ConvexPolyhedron) : P.dualGraph.Connected := by
  classical
  let surface := frontier P.body \ (P.vertices : Set Space)
  have connected := (P.frontier_diff_finite_pathConnected
    (P.vertices : Set Space) P.vertices.finite_toSet).isConnected
  obtain ⟨x, on_surface⟩ := connected.nonempty
  obtain ⟨some_face, _⟩ := P.boundary_point_in_face on_surface.1
  letI : Nonempty P.Face := ⟨some_face⟩
  refine ⟨?_⟩
  intro F G
  by_contra disconnected
  let reached := {H : P.Face // P.dualGraph.Reachable F H}
  let unreached := {H : P.Face // ¬ P.dualGraph.Reachable F H}
  let left : Set Space := ⋃ H : reached, H.val.val
  let right : Set Space := ⋃ H : unreached, H.val.val
  have left_closed : IsClosed left := isClosed_iUnion_of_finite (fun H => H.val.isClosed)
  have right_closed : IsClosed right := isClosed_iUnion_of_finite (fun H => H.val.isClosed)
  have cover : surface ⊆ left ∪ right := by
    intro y hy
    obtain ⟨H, hyH⟩ := P.boundary_point_in_face hy.1
    by_cases reachable : P.dualGraph.Reachable F H
    · exact Or.inl (Set.mem_iUnion.mpr ⟨⟨H, reachable⟩, hyH⟩)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨H, reachable⟩, hyH⟩)
  have left_nonempty : (surface ∩ left).Nonempty := by
    obtain ⟨y, hy, nonvertex⟩ := F.nonvertex_nonempty
    exact ⟨y, ⟨F.subset_frontier hy, nonvertex⟩,
      Set.mem_iUnion.mpr ⟨⟨F, SimpleGraph.Reachable.rfl⟩, hy⟩⟩
  have right_nonempty : (surface ∩ right).Nonempty := by
    obtain ⟨y, hy, nonvertex⟩ := G.nonvertex_nonempty
    exact ⟨y, ⟨G.subset_frontier hy, nonvertex⟩,
      Set.mem_iUnion.mpr ⟨⟨G, disconnected⟩, hy⟩⟩
  obtain ⟨y, on_surface, on_left, on_right⟩ := isPreconnected_closed_iff.mp connected.isPreconnected
    left right left_closed right_closed cover left_nonempty right_nonempty
  obtain ⟨A, y_in_A⟩ := Set.mem_iUnion.mp on_left
  obtain ⟨B, y_in_B⟩ := Set.mem_iUnion.mp on_right
  have distinct : A.val ≠ B.val := by
    intro equal
    exact B.property (equal ▸ A.property)
  have adjacent : P.dualGraph.Adj A.val B.val :=
    A.val.shareEdge_of_common_nonvertex B.val distinct ⟨y_in_A, y_in_B⟩ on_surface.2
  exact B.property (A.property.trans adjacent.reachable)

/-- A spanning tree of original face hinges exists for every public convex polyhedron. -/
theorem exists_hinge_tree (P : ConvexPolyhedron) :
    ∃ hinges : SimpleGraph P.Face, hinges ≤ P.dualGraph ∧ hinges.IsTree :=
  P.dualGraph_connected.exists_isTree_le

/-- Every such polyhedron has a rigid development with a tree of original hinges.
The remaining unfolding obligation is nonoverlap. -/
theorem exists_rigid_development (P : ConvexPolyhedron) :
    ∃ (hinges : SimpleGraph P.Face) (place : P.Face → Space →ᵃ[ℝ] Plane),
      hinges.IsTree ∧ hinges ≤ P.dualGraph ∧
      (∀ F, ∀ x ∈ F.val, ∀ y ∈ F.val, dist (place F x) (place F y) = dist x y) ∧
      (∀ F G, hinges.Adj F G → ∀ x ∈ F.val ∩ G.val, place F x = place G x) := by
  obtain ⟨hinges, original_edges, tree⟩ := P.exists_hinge_tree
  obtain ⟨place, rigid, joined⟩ := exists_tree_development P hinges tree original_edges
  exact ⟨hinges, place, tree, original_edges, rigid, joined⟩

end SixVertexUnfolding.ConvexPolyhedron
