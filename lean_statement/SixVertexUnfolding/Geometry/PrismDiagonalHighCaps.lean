import SixVertexUnfolding.Geometry.PrismDiagonalCaseA
import SixVertexUnfolding.Geometry.PrismDiagonalTwoViewCaseB

/-! The two-view fallback now handles both Case A and Case B. In particular,
it is an edge unfolding whenever both cap-curvature sums are at least π. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Prism Prism.FaceLabel Real

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4}
variable (prism_kind : graph.kind = .prismDiagonal)
include prism_kind small_faces

/-- Wider-angle tests in the narrow views suffice: a wide view is already covered by Case B. -/
theorem PrismFallbackDevelopment.quadrilaterals_of_two_view_bounds
    (net : graph.PrismFallbackDevelopment small_faces)
    (caseA_bounds : ∀ q : Fin 2, graph.prismCapOpening small_faces q < π →
      graph.prismAngle small_faces (capLeftFace q) (capSource q) ≤ (π + graph.prismCapOpening small_faces q) / 2 ∧
      graph.prismAngle small_faces (capRightFace q) (capSource q) ≤ (π + graph.prismCapOpening small_faces q) / 2) :
    Disjoint (interior (net.place B '' (graph.prismDiagonalFace small_faces B).val))
      (interior (net.place D '' (graph.prismDiagonalFace small_faces D).val)) := by
  have middle := graph.prism_middle_view_sum (small_faces := small_faces) prism_kind
  by_cases lower : π ≤ graph.prismAngle small_faces C 0 +
      (graph.prismAngle small_faces C 1 + graph.prismAngle small_faces E 1)
  · by_cases narrow : graph.prismCapOpening small_faces 0 < π
    · exact net.cap_caseA prism_kind 0 narrow (caseA_bounds 0 narrow).1 (caseA_bounds 0 narrow).2
    · have wide := le_of_not_gt narrow
      rw [graph.prismCapOpening_eq small_faces prism_kind 0] at wide
      exact (net.lower_caseB prism_kind wide lower).mono interior_subset interior_subset
  · have upper : π ≤ graph.prismAngle small_faces E 4 +
        (graph.prismAngle small_faces E 3 + graph.prismAngle small_faces C 3) := by linarith
    by_cases narrow : graph.prismCapOpening small_faces 1 < π
    · exact (net.cap_caseA prism_kind 1 narrow (caseA_bounds 1 narrow).1 (caseA_bounds 1 narrow).2).symm
    · have wide := le_of_not_gt narrow
      rw [graph.prismCapOpening_eq small_faces prism_kind 1] at wide
      exact (net.upper_caseB prism_kind wide upper).mono interior_subset interior_subset

/-- Both cap-curvature gates make the fixed fallback safe for all fifteen whole-face pairs. -/
theorem prismDiagonal_hasEdgeUnfolding_of_high_caps
    (lower_high : π ≤ graph.prismLowerCapCurvature)
    (upper_high : π ≤ graph.prismUpperCapCurvature) : P.HasEdgeUnfolding := by
  obtain ⟨net, other_pairs⟩ := graph.exists_prism_fallback_safe_except_quadrilaterals
    (small_faces := small_faces) prism_kind
  apply net.hasEdgeUnfolding_of_quadrilaterals prism_kind other_pairs
  apply net.quadrilaterals_of_two_view_bounds prism_kind
  intro q _
  have high : π ≤ graph.curvature (vertexLabel (capLeftVertex q)) +
      graph.curvature (vertexLabel (capRightVertex q)) + graph.curvature (vertexLabel (capSource q)) := by
    fin_cases q
    · exact lower_high
    · change π ≤ graph.curvature (vertexLabel 4) + graph.curvature (vertexLabel 3) + graph.curvature (vertexLabel 5)
      unfold prismUpperCapCurvature at upper_high
      linarith
  have source := graph.prism_cap_source_angles small_faces prism_kind q
  have left_bounds := graph.prismAngle_bounds small_faces prism_kind (capLeftFace q) (capSource q) (by fin_cases q <;> decide)
  have right_bounds := graph.prismAngle_bounds small_faces prism_kind (capRightFace q) (capSource q) (by fin_cases q <;> decide)
  constructor <;> unfold prismCapOpening <;>
    linarith [left_bounds.1, left_bounds.2, right_bounds.1, right_bounds.2]

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
