import SixVertexUnfolding.Geometry.PrismDiagonalHighCaps

/-! The fallback arm of Switch 1 now yields an actual edge unfolding.
Failure of the near-star's angle tests supplies the upper-view cone bounds. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Prism Prism.FaceLabel Real

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4}
variable (prism_kind : graph.kind = .prismDiagonal)
include prism_kind

/-- A safe lower cap and the two upper wider-angle tests make the fixed fallback a net. -/
theorem prismDiagonal_hasEdgeUnfolding_of_lower_cap_and_upper_bounds
    (lower_high : π ≤ graph.prismLowerCapCurvature)
    (upper_B : graph.prismFallbackDeficit small_faces B ≤ 0)
    (upper_D : graph.prismFallbackDeficit small_faces D ≤ 0) : P.HasEdgeUnfolding := by
  obtain ⟨net, other_pairs⟩ := graph.exists_prism_fallback_safe_except_quadrilaterals
    (small_faces := small_faces) prism_kind
  apply net.hasEdgeUnfolding_of_quadrilaterals prism_kind other_pairs
  apply net.quadrilaterals_of_two_view_bounds prism_kind
  intro q _
  fin_cases q
  · have bounds := graph.prism_lower_cap_wider_bounds small_faces prism_kind lower_high
    dsimp [prismCapOpening, capLeftFace, capRightFace, capFace, capSource, capLeftVertex, capRightVertex]
    exact ⟨by linarith [bounds.1], by linarith [bounds.2]⟩
  · unfold prismFallbackDeficit prismSwitchBaseCurvature at upper_B upper_D
    dsimp [prismCapOpening, capLeftFace, capRightFace, capFace, capSource, capLeftVertex, capRightVertex]
    exact ⟨by linarith, by linarith⟩

/-- The failed near-star tests force an actual fallback unfolding when vertex 2 is sharp. -/
theorem prismDiagonal_hasEdgeUnfolding_of_failed_near_tests
    (sharp : π ≤ graph.curvature (vertexLabel 2))
    (middle_obtuse : π / 2 < graph.prismAngle small_faces E 1)
    (near_fails : 0 < graph.prismNearDeficit small_faces D) : P.HasEdgeUnfolding := by
  have bounds := graph.prism_failed_near_forces_fallback_bounds small_faces prism_kind middle_obtuse near_fails
  have left_pos := graph.curvature_pos small_faces (vertexLabel 0)
  have right_pos := graph.curvature_pos small_faces (vertexLabel 1)
  apply graph.prismDiagonal_hasEdgeUnfolding_of_lower_cap_and_upper_bounds prism_kind
    (by unfold prismLowerCapCurvature; linarith) bounds.1.le bounds.2.le

/-- In the sharp-end branch, only the near-star's successful tests can remain unresolved. -/
theorem prismDiagonal_sharp_end_unfolding_or_near_tests
    (sharp : π ≤ graph.curvature (vertexLabel 2)) :
    P.HasEdgeUnfolding ∨ graph.prismAngle small_faces E 1 ≤ π / 2 ∨
      (graph.prismNearDeficit small_faces C ≤ 0 ∧ graph.prismNearDeficit small_faces D ≤ 0) := by
  by_cases middle : graph.prismAngle small_faces E 1 ≤ π / 2
  · exact Or.inr (Or.inl middle)
  · by_cases near : graph.prismNearDeficit small_faces D ≤ 0
    · exact Or.inr (Or.inr ⟨(graph.prism_near_C_deficit_neg small_faces prism_kind).le, near⟩)
    · exact Or.inl (graph.prismDiagonal_hasEdgeUnfolding_of_failed_near_tests prism_kind sharp
        (lt_of_not_ge middle) (lt_of_not_ge near))

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
