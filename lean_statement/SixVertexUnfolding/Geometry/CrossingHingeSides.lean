import SixVertexUnfolding.Geometry.HingeDeterminant
import SixVertexUnfolding.Geometry.JoinedTriangleInterior

/-! Crossing diagonals put the two remaining corners on opposite sides of their common hinge. -/

namespace SixVertexUnfolding

theorem oppositeHingeSides_of_crossing (a b c d q : Plane) (different : a ≠ b)
    (on_hinge : q ∈ segment ℝ a b) (crossing : q ∈ openSegment ℝ c d) :
    OppositeHingeSides a b c d := by
  rw [oppositeHingeSides_iff_det a b c d different]
  have zero : det (b - a) (q - a) = 0 := by
    obtain ⟨s, t, hs, ht, total, expression⟩ := on_hinge
    rw [segment_weighted_area a b a b q s t total expression]
    simp [det, mul_comm]
  obtain ⟨s, t, hs, ht, total, expression⟩ := crossing
  have height := segment_weighted_area a b c d q s t total expression
  rw [zero] at height
  by_cases positive : 0 ≤ det (b - a) (c - a)
  · have other : det (b - a) (d - a) ≤ 0 := by nlinarith [mul_nonneg hs.le positive]
    exact mul_nonpos_of_nonneg_of_nonpos positive other
  · have other : 0 ≤ det (b - a) (d - a) := by
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hs.le (le_of_not_ge positive)]
    exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge positive) other

end SixVertexUnfolding
