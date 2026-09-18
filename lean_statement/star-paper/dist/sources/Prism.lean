import Mathlib

/-! The cap budgets and gate selection in PRISM_CAP_RULE.md; no geometric net is assumed. -/

namespace SixVertexUnfolding.Prism

open Real

/-- At a degree-three source, the wider-angle deficit is a cap-curvature deficit. -/
theorem cap_identity {lam ρ ν kp K : ℝ}
    (source_sum : lam + ρ + ν = 2 * π - kp) :
    2 * lam + ν - 2 * π - K = lam - ρ - (kp + K) := by
  linarith

/-- A cap sum of at least pi supplies both wider Case A angle bounds. -/
theorem cap_wider_bounds {lam ρ ν kp K : ℝ}
    (source_sum : lam + ρ + ν = 2 * π - kp)
    (left_pos : 0 < lam) (left_lt : lam < π)
    (right_pos : 0 < ρ) (right_lt : ρ < π)
    (cap_high : π ≤ kp + K) :
    lam < (π + (π - ν + K)) / 2 ∧ ρ < (π + (π - ν + K)) / 2 := by
  constructor <;> linarith

/-- The two-cap decision includes the equality cases in the first branch. -/
theorem cap_cases {lower upper : ℝ} (total : lower + upper = 4 * π) :
    (π ≤ lower ∧ π ≤ upper) ∨
    (3 * π < lower ∧ upper < π) ∨
    (3 * π < upper ∧ lower < π) := by
  by_cases lower_high : π ≤ lower
  · by_cases upper_high : π ≤ upper
    · exact Or.inl ⟨lower_high, upper_high⟩
    · exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
  · exact Or.inr (Or.inr ⟨by linarith, by linarith⟩)

/-- A cap below pi has every positive constituent below pi. -/
theorem low_cap_vertices {a b c : ℝ}
    (a_pos : 0 < a) (b_pos : 0 < b) (c_pos : 0 < c)
    (cap_low : a + b + c < π) : a < π ∧ b < π ∧ c < π := by
  exact ⟨by linarith, by linarith, by linarith⟩

/-- The low-end branch of a high cap supplies both gates for Switch 2. -/
theorem high_cap_forces_gates {k0 k1 k2 : ℝ}
    (cap_high : 3 * π < k0 + k1 + k2)
    (vertex_bound : k1 < 2 * π) (end_low : k2 < π) :
    π < k0 + k2 ∧ 2 * π < k0 + k1 := by
  exact ⟨by linarith, by linarith⟩

/-- The two middle angles used by Switch 2 cannot both be obtuse. -/
theorem one_middle_angle_nonobtuse {a b c : ℝ}
    (triangle_sum : a + b + c = π) (third_pos : 0 < c) :
    a ≤ π / 2 ∨ b ≤ π / 2 := by
  by_cases first : a ≤ π / 2
  · exact Or.inl first
  · exact Or.inr (by linarith)

/-- One of the two views of the fallback has central angle at least pi. -/
theorem one_view_at_least_pi {lower upper : ℝ}
    (view_sum : lower + upper = 2 * π) : π ≤ lower ∨ π ≤ upper := by
  by_cases first : π ≤ lower
  · exact Or.inl first
  · exact Or.inr (by linarith)

end SixVertexUnfolding.Prism
