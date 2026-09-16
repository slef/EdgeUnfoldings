import SixVertexUnfolding.Geometry.PolarPointUniqueness

/-! Two inward-facing slit flanks cannot meet when both angular spans are below half the opened fan. -/

namespace SixVertexUnfolding

open Real EuclideanGeometry

/-- The side conditions choose the through-fan angular branch, even when the fan exceeds pi. -/
theorem inward_flanks_cannot_meet (r s Γ : ℝ) (r_pos : 0 < r) (s_pos : 0 < s)
    (fan_pos : 0 < Γ) (one_turn : Γ < 2 * π) (x : Plane) (nonzero : x ≠ 0)
    (first_side : 0 ≤ det (direction 0) x) (last_side : det (direction Γ) x ≤ 0)
    (first_span : 2 * angle (r • direction 0) 0 x < Γ)
    (last_span : 2 * angle x 0 (s • direction Γ) < Γ) : False := by
  let θ := angle (r • direction 0) 0 x
  let radius := dist 0 x
  have radius_pos : 0 < radius := dist_pos.mpr nonzero.symm
  have θ_nonnegative : 0 ≤ θ := angle_nonneg _ _ _
  have θ_le_pi : θ ≤ π := angle_le_pi _ _ _
  have θ_bound : 2 * θ < Γ := first_span
  have polar : x = radius • direction θ := by
    apply polar_point_eq_of_cos_and_side r radius 0 θ r_pos radius_pos x rfl
    · rw [sub_zero]
    · rw [sub_zero]
      exact mul_nonneg first_side (sin_nonneg_of_nonneg_of_le_pi θ_nonnegative θ_le_pi)
  have last_sine : sin (θ - Γ) ≤ 0 := by
    rw [polar, det_smul_right, direction_det] at last_side
    nlinarith
  have difference_pos : 0 < Γ - θ := by linarith
  have difference_small : Γ - θ ≤ π := by
    by_contra too_large
    have positive := sin_pos_of_pos_of_lt_pi
      (show 0 < θ - Γ + 2 * π by linarith) (show θ - Γ + 2 * π < π by linarith)
    rw [sin_add_two_pi] at positive
    linarith
  have last_angle : angle x 0 (s • direction Γ) = Γ - θ := by
    rw [polar]
    exact radial_angle radius s θ Γ radius_pos s_pos difference_pos.le difference_small
  rw [last_angle] at last_span
  linarith

/-- The signed heights against three directions obey the elementary sine interpolation identity. -/
theorem ray_height_interpolation (δ ρ κ : ℝ) (x : Plane) :
    sin ρ * det (direction (δ + κ)) x = sin κ * det (direction (δ + ρ)) x -
      sin (κ - ρ) * det (direction δ) x := by
  simp only [det, direction_x, direction_y, sin_add, cos_add, sin_sub]
  ring

/-- A flank whose extension is strictly inside the curvature gap cannot reach the opposite flank through that gap. -/
theorem short_gap_before (κ ρ : ℝ) (gap_pos : 0 < κ) (gap_small : κ < π)
    (reflex_pos : 0 < ρ) (short : ρ ≤ κ) (x : Plane)
    (below_start : det (direction 0) x < 0) (above_outer : 0 < det (direction (-ρ)) x)
    (below_end : det (direction (-κ)) x ≤ 0) : False := by
  have identity := ray_height_interpolation 0 (-ρ) (-κ) x
  have gap_sine := sin_pos_of_pos_of_lt_pi gap_pos gap_small
  have reflex_sine := sin_pos_of_pos_of_lt_pi reflex_pos (lt_of_le_of_lt short gap_small)
  have difference_sine : 0 ≤ sin (κ - ρ) := sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  rw [zero_add, zero_add, sin_neg, sin_neg, show -κ - -ρ = -(κ - ρ) by ring, sin_neg] at identity
  have positive := mul_pos gap_sine above_outer
  have nonpositive := mul_nonpos_of_nonneg_of_nonpos difference_sine below_start.le
  have other_nonpositive := mul_nonpos_of_nonneg_of_nonpos reflex_sine.le below_end
  nlinarith

theorem short_gap_after (δ κ ρ : ℝ) (gap_pos : 0 < κ) (gap_small : κ < π)
    (reflex_pos : 0 < ρ) (short : ρ ≤ κ) (x : Plane)
    (above_end : 0 < det (direction δ) x) (below_outer : det (direction (δ + ρ)) x < 0)
    (above_start : 0 ≤ det (direction (δ + κ)) x) : False := by
  have identity := ray_height_interpolation δ ρ κ x
  have gap_sine := sin_pos_of_pos_of_lt_pi gap_pos gap_small
  have reflex_sine := sin_pos_of_pos_of_lt_pi reflex_pos (lt_of_le_of_lt short gap_small)
  have difference_sine : 0 ≤ sin (κ - ρ) := sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have negative := mul_neg_of_pos_of_neg gap_sine below_outer
  have nonnegative := mul_nonneg difference_sine above_end.le
  have other_nonnegative := mul_nonneg reflex_sine.le above_start
  nlinarith

end SixVertexUnfolding
