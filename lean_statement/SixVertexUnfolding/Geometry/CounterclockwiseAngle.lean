import SixVertexUnfolding.Geometry.RadialSectorMembership

/-! A concrete angle in one full turn, expressed using the ordinary angle and the Cartesian determinant. -/

namespace SixVertexUnfolding

open Real EuclideanGeometry

/-- Counterclockwise angular distance between two nonzero rays, measured in radians. -/
noncomputable def counterclockwiseAngle (x y : Plane) : ℝ :=
  if det x y < 0 then 2 * π - InnerProductGeometry.angle x y else InnerProductGeometry.angle x y

/-- On positive polar representatives in one turn, this is exactly their direction difference. -/
theorem counterclockwiseAngle_polar (r s α β : ℝ) (r_pos : 0 < r) (s_pos : 0 < s)
    (lower : 0 ≤ β - α) (upper : β - α < 2 * π) :
    counterclockwiseAngle (r • direction α) (s • direction β) = β - α := by
  by_cases half_turn : β - α ≤ π
  · have nonnegative : 0 ≤ det (r • direction α) (s • direction β) := by
      rw [det_smul_left, det_smul_right, direction_det]
      exact mul_nonneg r_pos.le (mul_nonneg s_pos.le (sin_nonneg_of_nonneg_of_le_pi lower half_turn))
    unfold counterclockwiseAngle
    rw [if_neg (not_lt_of_ge nonnegative)]
    simpa only [EuclideanGeometry.angle, vsub_eq_sub, sub_zero] using radial_angle r s α β r_pos s_pos lower half_turn
  · have negative : det (r • direction α) (s • direction β) < 0 := by
      rw [det_smul_left, det_smul_right, direction_det]
      have sine := sin_neg_of_neg_of_neg_pi_lt (show β - α - 2 * π < 0 by linarith)
        (show -π < β - α - 2 * π by linarith)
      rw [sin_sub_two_pi] at sine
      exact mul_neg_of_pos_of_neg r_pos (mul_neg_of_pos_of_neg s_pos sine)
    have measured := radial_angle s r β (α + 2 * π) s_pos r_pos (by linarith) (by linarith)
    rw [direction_add_two_pi, angle_comm] at measured
    simp only [EuclideanGeometry.angle, vsub_eq_sub, sub_zero] at measured
    unfold counterclockwiseAngle
    rw [if_pos negative]
    rw [measured]
    ring

end SixVertexUnfolding
