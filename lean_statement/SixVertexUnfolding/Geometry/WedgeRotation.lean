import SixVertexUnfolding.Geometry.WedgeRootMove

/-! A broken wedge arm meets each circle about its root exactly once.
This gives an explicit polar description of the arm-rotation step.
The outer ray must point away from the root; in Kiazyk's notation this
is the condition `π/2 ≤ γ ≤ 3π/2`.
-/

namespace SixVertexUnfolding.Wedge

open Real Set

/-- Distance along an outward unit ray, from an elbow of radius `d`
to the circle of radius `ρ`. Here `(c,s)` is the ray's unit direction
relative to the radial direction of the elbow. -/
noncomputable def travel (d c s ρ : ℝ) : ℝ :=
  sqrt (ρ ^ 2 - d ^ 2 * s ^ 2) - d * c

/-- The square-root formula gives a nonnegative distance and a point on the circle. -/
theorem travel_spec {d c s ρ : ℝ} (dp : 0 < d) (outward : 0 ≤ c)
    (unit : c ^ 2 + s ^ 2 = 1) (outside : d ≤ ρ) :
    0 ≤ travel d c s ρ ∧
      (d + travel d c s ρ * c) ^ 2 + (travel d c s ρ * s) ^ 2 = ρ ^ 2 := by
  have dc : 0 ≤ d * c := mul_nonneg dp.le outward
  have scaled : d ^ 2 * c ^ 2 + d ^ 2 * s ^ 2 = d ^ 2 := by
    nlinarith [congrArg (fun x : ℝ => d ^ 2 * x) unit]
  have radicand : 0 ≤ ρ ^ 2 - d ^ 2 * s ^ 2 := by nlinarith [sq_nonneg (d * c)]
  have root_nonneg := sqrt_nonneg (ρ ^ 2 - d ^ 2 * s ^ 2)
  have root_square := sq_sqrt radicand
  have root_bound : d * c ≤ sqrt (ρ ^ 2 - d ^ 2 * s ^ 2) := by nlinarith
  refine ⟨sub_nonneg.mpr root_bound, ?_⟩
  have scaled' := congrArg (fun x : ℝ => (travel d c s ρ) ^ 2 * x) unit
  have equation : (travel d c s ρ) ^ 2 + 2 * d * c * travel d c s ρ = ρ ^ 2 - d ^ 2 := by
    unfold travel
    nlinarith
  nlinarith

/-- A point on the right half of a circle has these exact Cartesian polar coordinates. -/
private theorem polar_of_right_circle {ρ x y : ℝ} (rp : 0 < ρ) (xp : 0 ≤ x)
    (circle : x ^ 2 + y ^ 2 = ρ ^ 2) :
    ρ * cos (arcsin (y / ρ)) = x ∧ ρ * sin (arcsin (y / ρ)) = y := by
  have low : -1 ≤ y / ρ := (le_div_iff₀ rp).mpr (by nlinarith [sq_nonneg x])
  have high : y / ρ ≤ 1 := (div_le_iff₀ rp).mpr (by nlinarith [sq_nonneg x])
  have sine : ρ * sin (arcsin (y / ρ)) = y := by
    rw [sin_arcsin low high]
    field_simp
  refine ⟨?_, sine⟩
  have cosine := cos_nonneg_of_mem_Icc (arcsin_mem_Icc (y / ρ))
  have scaled := congrArg (fun a : ℝ => ρ ^ 2 * a) (cos_sq_add_sin_sq (arcsin (y / ρ)))
  have positive := mul_nonneg rp.le cosine
  nlinarith [congrArg (fun a : ℝ => a ^ 2) sine]

/-- At every radius outside the elbow, the displayed angle lies on the actual straight ray. -/
theorem ray_polar_coordinates {d c s ρ : ℝ} (dp : 0 < d) (outward : 0 ≤ c)
    (unit : c ^ 2 + s ^ 2 = 1) (outside : d ≤ ρ) :
    ρ * cos (arcsin (travel d c s ρ * s / ρ)) = d + travel d c s ρ * c ∧
    ρ * sin (arcsin (travel d c s ρ * s / ρ)) = travel d c s ρ * s := by
  have spec := travel_spec dp outward unit outside
  exact polar_of_right_circle (dp.trans_le outside)
    (add_nonneg dp.le (mul_nonneg spec.1 outward)) spec.2

/-- An outward ray cannot meet the same circle twice. -/
theorem ray_circle_unique {d c s ρ t : ℝ} (dp : 0 < d) (outward : 0 ≤ c)
    (unit : c ^ 2 + s ^ 2 = 1) (outside : d ≤ ρ) (tp : 0 ≤ t)
    (circle : (d + t * c) ^ 2 + (t * s) ^ 2 = ρ ^ 2) :
    t = travel d c s ρ := by
  have spec := travel_spec dp outward unit outside
  have scaled₁ := congrArg (fun x : ℝ => t ^ 2 * x) unit
  have scaled₂ := congrArg (fun x : ℝ => (travel d c s ρ) ^ 2 * x) unit
  have dc := mul_nonneg dp.le outward
  rcases lt_trichotomy t (travel d c s ρ) with less | same | greater
  · have strict := mul_pos (sub_pos.mpr less)
      (show 0 < t + travel d c s ρ + 2 * d * c by nlinarith)
    nlinarith
  · exact same
  · have strict := mul_pos (sub_pos.mpr greater)
      (show 0 < t + travel d c s ρ + 2 * d * c by nlinarith)
    nlinarith

/-- Angular displacement from an inner leg on the circle of radius `ρ`.
It is zero before the elbow, and follows the straight outer ray afterwards. -/
noncomputable def offset (d γ ρ : ℝ) : ℝ :=
  if ρ < d then 0 else
    arcsin (travel d (cos (π - γ)) (sin (π - γ)) ρ * sin (π - γ) / ρ)

/-- Before the elbow the boundary is the original radial segment. -/
theorem inner_arm {d γ ρ : ℝ} (inside : ρ < d) (θ : ℝ) :
    ρ • direction (θ + offset d γ ρ) = ρ • direction θ := by
  simp [offset, inside]

/-- The polar and straight pieces agree at the elbow, including tangent rays. -/
theorem offset_at_elbow {d γ : ℝ} (dp : 0 < d)
    (lower : π / 2 ≤ γ) (upper : γ ≤ 3 * π / 2) : offset d γ d = 0 := by
  have outward : 0 ≤ cos (π - γ) := cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  have travel_zero := ray_circle_unique dp outward (cos_sq_add_sin_sq (π - γ))
    le_rfl (le_refl 0) (by simp : (d + 0 * cos (π - γ)) ^ 2 + (0 * sin (π - γ)) ^ 2 = d ^ 2)
  unfold offset
  rw [if_neg (lt_irrefl d), ← travel_zero]
  simp

/-- Reflection reverses the displacement, so the other arm uses `-offset`. -/
theorem offset_reflected (d γ ρ : ℝ) : offset d (2 * π - γ) ρ = -offset d γ ρ := by
  unfold offset
  split_ifs with inside
  · simp
  · rw [show π - (2 * π - γ) = -(π - γ) by ring, cos_neg, sin_neg]
    simp [travel, neg_div, arcsin_neg]

/-- Exact boundary points after rotating an arm through `θ`. -/
theorem outer_arm {d γ ρ : ℝ} (dp : 0 < d)
    (lower : π / 2 ≤ γ) (upper : γ ≤ 3 * π / 2) (outside : d ≤ ρ) (θ : ℝ) :
    ρ • direction (θ + offset d γ ρ) =
      d • direction θ + travel d (cos (π - γ)) (sin (π - γ)) ρ • direction (θ + (π - γ)) := by
  have outward : 0 ≤ cos (π - γ) := cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  have polar := ray_polar_coordinates dp outward (cos_sq_add_sin_sq (π - γ)) outside
  simp only [cos_pi_sub, sin_pi_sub] at polar
  unfold offset
  rw [if_neg (not_lt_of_ge outside)]
  ext i
  fin_cases i <;>
    simp [direction, PiLp.smul_apply, PiLp.add_apply, cos_add, sin_add]
  · nlinarith [congrArg (fun x : ℝ => cos θ * x) polar.1,
      congrArg (fun x : ℝ => sin θ * x) polar.2]
  · nlinarith [congrArg (fun x : ℝ => sin θ * x) polar.1,
      congrArg (fun x : ℝ => cos θ * x) polar.2]

/-- The region between the two broken arms, described circle by circle.
An empty angular interval gives an empty circle section; a full turn gives
the whole circle. Thus bounded and unbounded wedges use the same formula. -/
noncomputable def polarRegion (d γ lower upper : ℝ) : Set Plane := {z |
  z = 0 ∨ ∃ ρ θ : ℝ, 0 < ρ ∧ z = ρ • direction θ ∧
    lower + offset d γ ρ ≤ θ ∧ θ ≤ upper - offset d γ ρ}

/-- Rotating either arm away from the region only enlarges it.
`outer_arm` verifies that the circle sections follow the actual straight rays. -/
theorem rotate_arms {d γ lower₁ upper₁ lower₂ upper₂ : ℝ}
    (lower_moves : lower₂ ≤ lower₁) (upper_moves : upper₁ ≤ upper₂) :
    polarRegion d γ lower₁ upper₁ ⊆ polarRegion d γ lower₂ upper₂ := by
  rintro z (zero | ⟨ρ, θ, positive, position, left, right⟩)
  · exact Or.inl zero
  · exact Or.inr ⟨ρ, θ, positive, position, by linarith, by linarith⟩

end SixVertexUnfolding.Wedge
