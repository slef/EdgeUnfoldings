import SixVertexUnfolding.Curvature.Obstructions

/-! The trigonometric consequence of closed finite-cut contact, with endpoint equalities included. -/

namespace SixVertexUnfolding.Contact

open Real

/-- On the positive sine arc, an increase across a positive gap bounds the sum of the arguments. -/
theorem sine_comparison_sum {a b : ℝ} (a_pos : 0 < a) (ordered : a < b) (b_small : b < π)
    (comparison : sin a ≤ sin b) : a + b ≤ π := by
  have difference : 0 ≤ 2 * cos ((b + a) / 2) * sin ((b - a) / 2) := by
    nlinarith [sin_sub_sin b a]
  have sine_positive : 0 < sin ((b - a) / 2) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have cosine_nonnegative : 0 ≤ cos ((b + a) / 2) := by nlinarith
  by_contra too_large
  have angle_gt : π / 2 < (b + a) / 2 := by linarith [lt_of_not_ge too_large]
  have cosine_negative := strictAntiOn_cos
    (show π / 2 ∈ Set.Icc (0 : ℝ) π from ⟨by positivity, by linarith [pi_pos]⟩)
    (show (b + a) / 2 ∈ Set.Icc (0 : ℝ) π from ⟨by linarith, by linarith⟩) angle_gt
  rw [cos_pi_div_two] at cosine_negative
  linarith

/-- The first contact may be the petal apex: only the closed bound `t ≤ 1` is used. -/
theorem finite_contact_angle_bound {r s t θ δ gap : ℝ}
    (s_pos : 0 < s) (t_le : t ≤ 1) (gap_pos : 0 < gap)
    (angle_pos : 0 < θ + δ) (angle_small : θ + gap + δ < π)
    (on_cut : r * sin δ = t * s * sin (θ + gap + δ))
    (contained : s * sin (θ + δ) ≤ r * sin δ) : 2 * θ + 2 * δ + gap ≤ π := by
  have sine_positive : 0 < sin (θ + gap + δ) := sin_pos_of_pos_of_lt_pi (by linarith) angle_small
  have scaled : t * s * sin (θ + gap + δ) ≤ s * sin (θ + gap + δ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr t_le) (mul_pos s_pos sine_positive).le]
  have comparison : sin (θ + δ) ≤ sin (θ + gap + δ) := by nlinarith
  have sum_bound := sine_comparison_sum angle_pos (by linarith : θ + δ < θ + gap + δ) angle_small comparison
  linarith

/-- The strict closed-link estimate turns the non-strict contact angle bound into the strict curvature obstruction. -/
theorem finite_contact_curvature_budget {r s t θ δ ka kc kw μ γ : ℝ}
    (s_pos : 0 < s) (t_le : t ≤ 1) (gap_pos : 0 < ka)
    (angle_pos : 0 < θ + δ) (angle_small : θ + ka + δ < π)
    (on_cut : r * sin δ = t * s * sin (θ + ka + δ))
    (contained : s * sin (θ + δ) ≤ r * sin δ)
    (angle_sum : θ + δ = π - γ + μ + kw) (strict_link : 2 * γ < 2 * π - kc) :
    ka + kc + 2 * kw + 2 * μ < π :=
  Curvature.finite_contact_budget
    (finite_contact_angle_bound s_pos t_le gap_pos angle_pos angle_small on_cut contained) angle_sum strict_link

end SixVertexUnfolding.Contact
