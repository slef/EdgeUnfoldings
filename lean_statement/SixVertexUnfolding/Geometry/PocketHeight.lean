import SixVertexUnfolding.Geometry.ConeHalfplanes
import SixVertexUnfolding.Geometry.DirectionIdentities

/-! In the small-fan branch, any meeting of the two base cones lies strictly below their common base. -/

namespace SixVertexUnfolding

open Real

/-- Eliminate the horizontal coordinate from the two outer-edge inequalities. -/
theorem pocket_height_negative (base σ τ : ℝ) (x : Plane)
    (base_pos : 0 < base) (σ_pos : 0 < σ) (τ_pos : 0 < τ) (small : σ + τ < π)
    (left : sin σ * x 0 + cos σ * x 1 ≤ 0)
    (right : 0 ≤ sin τ * (x 0 - base) - cos τ * x 1) : x 1 < 0 := by
  have sine_σ := sin_pos_of_pos_of_lt_pi σ_pos (by linarith)
  have sine_τ := sin_pos_of_pos_of_lt_pi τ_pos (by linarith)
  have sine_sum := sin_pos_of_pos_of_lt_pi (add_pos σ_pos τ_pos) small
  have first := mul_nonpos_of_nonneg_of_nonpos sine_τ.le left
  have second := mul_nonneg sine_σ.le right
  have identity : sin τ * (sin σ * x 0 + cos σ * x 1) -
      sin σ * (sin τ * (x 0 - base) - cos τ * x 1) =
        sin (σ + τ) * x 1 + base * sin σ * sin τ := by rw [sin_add]; ring
  have combined : sin (σ + τ) * x 1 + base * sin σ * sin τ ≤ 0 := by linarith
  have constant_pos := mul_pos (mul_pos base_pos sine_σ) sine_τ
  nlinarith

theorem sine_nonpositive_second_half (a : ℝ) (lower : π ≤ a) (upper : a ≤ 2 * π) : sin a ≤ 0 := by
  have nonnegative := sin_nonneg_of_nonneg_of_le_pi (show 0 ≤ a - π by linarith) (show a - π ≤ π by linarith)
  rw [sin_sub_pi] at nonnegative
  linarith

/-- This bound applies to the whole closed cones, so it also covers boundary meetings. -/
theorem base_cones_pocket_below (base α β σ τ : ℝ) (base_pos : 0 < base)
    (σ_pos : 0 < σ) (τ_pos : 0 < τ) (small : σ + τ < π)
    (left_bounds : π ≤ α + σ ∧ α + σ ≤ 2 * π)
    (right_bounds : π ≤ β + τ ∧ β + τ ≤ 2 * π)
    (x : Plane) (left : x ∈ translatedCone 0 (direction α) (direction (2 * π - σ)))
    (right : x ∈ translatedCone (base • direction 0) (direction (τ - π)) (direction (π - β))) :
    x 1 < 0 := by
  have left_sine := sine_nonpositive_second_half (α + σ) left_bounds.1 left_bounds.2
  have right_sine := sine_nonpositive_second_half (β + τ) right_bounds.1 right_bounds.2
  have left_side : det (direction (2 * π - σ)) x ≤ 0 := by
    obtain ⟨u, v, hu, _, expression⟩ := left
    rw [sub_zero] at expression
    rw [expression, det_add_right, det_smul_right, det_smul_right, det_self, mul_zero, add_zero, direction_det]
    rw [show α - (2 * π - σ) = (α + σ) - 2 * π by ring, sin_sub_two_pi]
    exact mul_nonpos_of_nonneg_of_nonpos hu left_sine
  have right_side : 0 ≤ det (direction (τ - π)) (x - base • direction 0) := by
    obtain ⟨u, v, _, hv, expression⟩ := right
    rw [expression, det_add_right, det_smul_right, det_smul_right, det_self, mul_zero, zero_add, direction_det]
    rw [show (π - β) - (τ - π) = -(β + τ) + 2 * π by ring, sin_add_two_pi, sin_neg]
    exact mul_nonneg hv (neg_nonneg.mpr right_sine)
  apply pocket_height_negative base σ τ x base_pos σ_pos τ_pos small
  · rw [direction_two_pi_sub] at left_side
    simpa only [det, direction_x, direction_y, cos_neg, sin_neg, neg_mul, sub_neg_eq_add, add_comm] using left_side
  · simpa only [det, direction_x, direction_y, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
      cos_sub_pi, sin_sub_pi, cos_zero, sin_zero, mul_one, mul_zero, sub_zero,
      neg_mul, sub_neg_eq_add, neg_add_rev, add_comm] using right_side

end SixVertexUnfolding
