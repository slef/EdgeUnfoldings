import SixVertexUnfolding.Geometry.StarCutsOnFaces

/-! Affine face placements agreeing with the star map agree on every
retained hinge, including its removed original endpoints by continuity. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- One retained adjacency joins the two rigid placements along the entire original edge. -/
theorem retained_hinge_agreement {P : ConvexPolyhedron} {a : frontier P.body}
    (develop : P.UncutSurface a → Plane) (F G : P.Face)
    (left right : Space →ᵃ[ℝ] Plane)
    (left_agrees : ∀ b : P.UncutSurface a, (b.val : Space) ∈ F.val → left b.val = develop b)
    (right_agrees : ∀ b : P.UncutSurface a, (b.val : Space) ∈ G.val → right b.val = develop b)
    (adjacent : (P.retainedFaceGraph a).Adj F G) :
    ∀ x ∈ F.val ∩ G.val, left x = right x := by
  have shared := P.retainedFaceGraph_original a adjacent
  obtain ⟨u, _, v, _, distinct, edge⟩ := F.shared_edge_endpoints G shared
  have open_agrees : EqOn left right (openSegment ℝ u v) := by
    intro x inside
    have common : x ∈ F.val ∩ G.val := by rw [edge]; exact openSegment_subset_segment ℝ u v inside
    have nonvertex : x ∉ P.vertices := by
      intro original
      have endpoints : u ∈ F.val ∩ G.val ∧ v ∈ F.val ∩ G.val := by
        rw [edge]; exact ⟨left_mem_segment ℝ _ _, right_mem_segment ℝ _ _⟩
      rcases P.vertex_in_segment_is_endpoint original (F.subset_body endpoints.1.1)
        (F.subset_body endpoints.2.1) (openSegment_subset_segment ℝ u v inside) with same | same
      · exact distinct (left_mem_openSegment_iff.mp (same.symm ▸ inside))
      · exact distinct (right_mem_openSegment_iff.mp (same.symm ▸ inside))
    let b : P.UncutSurface a := ⟨⟨x, F.subset_frontier common.1⟩,
      retained_edge_nonvertex_uncut F G adjacent _ common nonvertex⟩
    exact (left_agrees b common.1).trans (right_agrees b common.2).symm
  have closed_agrees := open_agrees.closure left.continuous_of_finiteDimensional right.continuous_of_finiteDimensional
  intro x common
  apply closed_agrees
  rw [closure_openSegment]
  rwa [← edge]

end SixVertexUnfolding.ConvexPolyhedron
