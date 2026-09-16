import Mathlib

/-!
The scalar consequences of finite-cut contact and small-fan overlap in TIDY_CORE.md.
The contact-containment, spherical-link, and pocket lemmas themselves are still
geometric obligations. These results prove the contradictions once those bounds hold.
-/

namespace SixVertexUnfolding.Curvature

open Real

/-- The strict link inequality makes the contact budget strict, even at boundary contact. -/
theorem finite_contact_budget
    {θ δ ka kc kw μ γ : ℝ}
    (contact_bound : 2 * θ + 2 * δ + ka ≤ π)
    (angle_sum : θ + δ = π - γ + μ + kw)
    (strict_link : 2 * γ < 2 * π - kc) :
    ka + kc + 2 * kw + 2 * μ < π := by
  linarith

/-- Either source branch of criterion (P) contradicts the two contact obstructions. -/
theorem finite_contact_impossible
    {kv kw ka kc μ : ℝ}
    (source_or_face : π ≤ kv ∨ π ≤ ka + kc + kw)
    (fan_pos : 0 < kw) (angle_pos : 0 < μ)
    (contact_E1 : kv < π)
    (contact_E2 : ka + kc + 2 * kw + 2 * μ < π) : False := by
  rcases source_or_face with source_high | face_high <;> linarith

/-- The same criterion excludes the small-fan pocket obstruction. -/
theorem small_fan_pocket_impossible
    {kv kw ka kc ν : ℝ}
    (source_or_face : π ≤ kv ∨ π ≤ ka + kc + kw)
    (source_pos : 0 < kv) (fan_pos : 0 < kw) (base_pos : 0 < ka)
    (slit_threshold : π ≤ 2 * kc + kw)
    (strict_link : 2 * ν < 2 * π - kv)
    (pocket : ka + kc + kw < ν) : False := by
  rcases source_or_face with source_high | face_high <;> linarith

end SixVertexUnfolding.Curvature
