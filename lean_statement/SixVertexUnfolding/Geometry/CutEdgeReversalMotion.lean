import SixVertexUnfolding.Geometry.CutEdgeCornerAngles
import SixVertexUnfolding.Geometry.BisectorSourceUniqueness

/-! Oppositely oriented models of one cut edge describe the same metric
kite. One rigid motion moves all four corners simultaneously. -/

namespace SixVertexUnfolding.ConvexPolyhedron.CutEdgeMetricModel

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a}
    {u v : T.vertices} {edge : T.graph.Adj u v} (M : CutEdgeMetricModel T edge)

/-- Reverse the base while retaining a chosen correspondence of source labels. -/
theorem exists_reversal_motion (N : CutEdgeMetricModel T edge.symm) :
    ∃ motion : Plane ≃ᵃⁱ[ℝ] Plane, motion M.left = N.right ∧ motion M.right = N.left ∧
      motion M.first = N.first ∧ motion M.second = N.second := by
  apply exists_bisector_motion M.left M.right M.first M.second N.right N.left N.first N.second
    N.base_different.symm M.distinct_sources N.distinct_sources
  · rw [M.base_length, dist_comm N.right N.left, N.base_length, dist_comm (v : Space) (u : Space)]
  · exact M.left_radius.trans N.right_radius.symm
  · exact M.right_radius.trans N.left_radius.symm
  · exact M.left_distances
  · exact M.right_distances
  · exact N.right_distances
  · exact N.left_distances

/-- The other allowed correspondence swaps both source labels together. -/
theorem exists_swapped_reversal_motion (N : CutEdgeMetricModel T edge.symm) :
    ∃ motion : Plane ≃ᵃⁱ[ℝ] Plane, motion M.left = N.right ∧ motion M.right = N.left ∧
      motion M.first = N.second ∧ motion M.second = N.first := by
  let swapped : CutEdgeMetricModel T edge.symm := {
    N with first := N.second
           second := N.first
           distinct_sources := N.distinct_sources.symm
           first_distances := N.second_distances
           second_distances := N.first_distances }
  exact M.exists_reversal_motion swapped

end SixVertexUnfolding.ConvexPolyhedron.CutEdgeMetricModel
