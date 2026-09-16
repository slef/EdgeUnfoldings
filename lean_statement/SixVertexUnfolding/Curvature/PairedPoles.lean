import SixVertexUnfolding.Curvature.Selection

/-!
The positive-remainder identity in PAIRED_POLE_RULE.md.
`lam, ν, ρ` are the three petal apex angles; `η` is the fourth petal's apex.
`ξ, ζ` are its base angles, at vertices with curvatures `ka, kb`.
`K` is the sum of the other two equator curvatures.
The spherical-link inequalities are explicit hypotheses, not asserted here.
-/

namespace SixVertexUnfolding.PairedPoles

open Real

noncomputable def linkSlack (curvature angle : ℝ) : ℝ :=
  (2 * π - curvature) - 2 * angle

variable {kv kw K ka kb η lam ν ρ ξ ζ : ℝ}

/-- Eliminate the fourth petal and the complementary curvatures. -/
theorem left_remainder_identity
    (source_sum : η + lam + ν + ρ = 2 * π - kv)
    (fourth_triangle : ξ + ζ = π - η)
    (total_curvature : kv + kw + K + ka + kb = 4 * π) :
    2 * π + K - 2 * lam - ν =
      (kv - kw) + (linkSlack ka ξ + linkSlack kb ζ) + ν + 2 * ρ := by
  unfold linkSlack
  linarith

theorem right_remainder_identity
    (source_sum : η + lam + ν + ρ = 2 * π - kv)
    (fourth_triangle : ξ + ζ = π - η)
    (total_curvature : kv + kw + K + ka + kb = 4 * π) :
    2 * π + K - 2 * ρ - ν =
      (kv - kw) + (linkSlack ka ξ + linkSlack kb ζ) + ν + 2 * lam := by
  unfold linkSlack
  linarith

/-- Source order and the fourth petal's strict link bounds give both Case A bounds. -/
theorem wider_caseA_bounds
    (source_sum : η + lam + ν + ρ = 2 * π - kv)
    (fourth_triangle : ξ + ζ = π - η)
    (total_curvature : kv + kw + K + ka + kb = 4 * π)
    (source_order : kw ≤ kv)
    (left_pos : 0 < lam) (middle_pos : 0 < ν) (right_pos : 0 < ρ)
    (link_a : 0 < linkSlack ka ξ) (link_b : 0 < linkSlack kb ζ) :
    lam < (π + (π - ν + K)) / 2 ∧ ρ < (π + (π - ν + K)) / 2 := by
  have left_identity := left_remainder_identity source_sum fourth_triangle total_curvature
  have right_identity := right_remainder_identity source_sum fourth_triangle total_curvature
  constructor <;> linarith

/-- The additional angle-sum premise follows from the omitted fourth petal. -/
theorem caseA_angle_sum
    (source_sum : η + lam + ν + ρ = 2 * π - kv)
    (fourth_pos : 0 < η) (source_pos : 0 < kv) (base_pos : 0 < K) :
    lam + ρ + ν < 2 * π + K := by
  linarith

end SixVertexUnfolding.PairedPoles
