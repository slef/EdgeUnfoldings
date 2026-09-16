import SixVertexUnfolding.Geometry.WedgeLevel

/-! On each upper semicircle there is exactly the boundary angle predicted
by the polar description. This identifies all possible sign changes.
-/

namespace SixVertexUnfolding.Wedge

open Real Set

/-- Coordinates for the same upper arm in the chord and root frames. -/
structure ArmCoordinates (h r a b d θ γ : ℝ) : Prop where
  radius_pos : 0 < d
  angle_pos : 0 < θ
  angle_lt_pi : θ < π
  lower : π / 2 ≤ γ
  upper : γ ≤ 3 * π / 2
  source_x : -r = d * cos θ
  source_y : h = d * sin θ
  ray_x : a = d * cos (θ + (π - γ))
  ray_y : b = d * sin (θ + (π - γ))

namespace ArmCoordinates

variable {h r a b d θ γ : ℝ} (C : ArmCoordinates h r a b d θ γ)

include C

theorem height_pos : 0 < h := by
  rw [C.source_y]
  exact mul_pos C.radius_pos (sin_pos_of_pos_of_lt_pi C.angle_pos C.angle_lt_pi)

theorem source_square : r ^ 2 + h ^ 2 = d ^ 2 := by
  have scaled := congrArg (fun x : ℝ => d ^ 2 * x) (cos_sq_add_sin_sq θ)
  nlinarith [congrArg (fun x : ℝ => x ^ 2) C.source_x,
    congrArg (fun x : ℝ => x ^ 2) C.source_y]

theorem ray_square : a ^ 2 + b ^ 2 = d ^ 2 := by
  have scaled := congrArg (fun x : ℝ => d ^ 2 * x) (cos_sq_add_sin_sq (θ + (π - γ)))
  nlinarith [congrArg (fun x : ℝ => x ^ 2) C.ray_x,
    congrArg (fun x : ℝ => x ^ 2) C.ray_y]

theorem outward_eq : h * b - r * a = d ^ 2 * cos (π - γ) := by
  have cosine := congrArg (fun x : ℝ => d ^ 2 * x) (cos_sub (θ + (π - γ)) θ)
  rw [add_sub_cancel_left] at cosine
  rw [C.source_y, show r = -(d * cos θ) by linarith [C.source_x], C.ray_x, C.ray_y]
  nlinarith

theorem outward : 0 ≤ h * b - r * a := by
  rw [C.outward_eq]
  exact mul_nonneg (sq_nonneg d) (cos_nonneg_of_mem_Icc ⟨by linarith [C.lower, C.upper], by linarith [C.lower, C.upper]⟩)

theorem ray_nonzero : a ≠ 0 ∨ b ≠ 0 := by
  by_contra missing
  push Not at missing
  have square := C.ray_square
  rw [missing.1, missing.2] at square
  nlinarith [C.radius_pos]

omit C in
theorem circle_square (ρ φ : ℝ) :
    (r + ρ * cos φ - r) ^ 2 + (ρ * sin φ) ^ 2 = ρ ^ 2 := by
  have scaled := congrArg (fun x : ℝ => ρ ^ 2 * x) (cos_sq_add_sin_sq φ)
  nlinarith

/-- The whole possible angular displacement is less than a quarter turn. -/
theorem boundary_angle_bounds (ρ : ℝ) :
    -π / 2 < θ + offset d γ ρ ∧ θ + offset d γ ρ < 3 * π / 2 := by
  unfold offset
  split_ifs
  · constructor <;> linarith [C.angle_pos, C.angle_lt_pi, pi_pos]
  · have low := neg_pi_div_two_le_arcsin
      (travel d (cos (π - γ)) (sin (π - γ)) ρ * sin (π - γ) / ρ)
    have high := arcsin_le_pi_div_two
      (travel d (cos (π - γ)) (sin (π - γ)) ρ * sin (π - γ) / ρ)
    constructor <;> linarith [C.angle_pos, C.angle_lt_pi]

private theorem boundary_angle_in_half {ρ : ℝ}
    (positive_sine : 0 ≤ sin (θ + offset d γ ρ)) : θ + offset d γ ρ ∈ Icc 0 π := by
  have bounds := C.boundary_angle_bounds ρ
  constructor
  · by_contra negative
    have bad := sin_neg_of_neg_of_neg_pi_lt (lt_of_not_ge negative) (by linarith [pi_pos])
    linarith
  · by_contra after
    have bad := sin_neg_of_neg_of_neg_pi_lt
      (show θ + offset d γ ρ - 2 * π < 0 by linarith [pi_pos])
      (show -π < θ + offset d γ ρ - 2 * π by linarith)
    rw [sin_sub_two_pi] at bad
    linarith

/-- A zero on an inner leg has the original source direction. -/
private theorem inner_zero_angle {ρ φ : ℝ} (rp : 0 < ρ) (ph : φ ∈ Icc 0 π)
    (inner : h * (r + ρ * cos φ) = r * (h - ρ * sin φ)) : φ = θ := by
  have sine : sin (θ - φ) = 0 := by
    rw [sin_sub]
    have product : d * ρ * (sin θ * cos φ - cos θ * sin φ) = 0 := by
      rw [C.source_y, show r = -(d * cos θ) by linarith [C.source_x]] at inner
      nlinarith
    exact (mul_eq_zero.mp product).resolve_left (ne_of_gt (mul_pos C.radius_pos rp))
  have equal := (sin_eq_zero_iff_of_lt_of_lt
    (by linarith [C.angle_pos, ph.2]) (by linarith [C.angle_lt_pi, ph.1])).mp sine
  linarith

/-- Recover the unique distance along the outer ray from any point on its circle. -/
private theorem outer_parameter {ρ t : ℝ} (rp : 0 < ρ) (tp : 0 ≤ t)
    (circle : (t * a - r) ^ 2 + (h + t * b) ^ 2 = ρ ^ 2) :
    d ≤ ρ ∧ t * d = travel d (cos (π - γ)) (sin (π - γ)) ρ := by
  have source := C.source_square
  have ray := C.ray_square
  have dot := C.outward_eq
  have w := C.outward
  have expanded : d ^ 2 + t ^ 2 * d ^ 2 + 2 * t * (h * b - r * a) = ρ ^ 2 := by
    nlinarith [congrArg (fun x : ℝ => t ^ 2 * x) ray]
  have outside : d ≤ ρ := by
    nlinarith [mul_nonneg tp w, mul_nonneg (sq_nonneg t) (sq_nonneg d), C.radius_pos]
  refine ⟨outside, ?_⟩
  apply ray_circle_unique C.radius_pos
    (cos_nonneg_of_mem_Icc ⟨by linarith [C.lower, C.upper], by linarith [C.lower, C.upper]⟩)
    (cos_sq_add_sin_sq (π - γ)) outside (mul_nonneg tp C.radius_pos.le)
  have unit := congrArg (fun x : ℝ => (t * d) ^ 2 * x) (cos_sq_add_sin_sq (π - γ))
  nlinarith [congrArg (fun x : ℝ => 2 * t * x) dot]

/-- The predicted outer boundary point is on the physical ray in the chord frame. -/
theorem boundary_ray_point {ρ : ℝ} (outside : d ≤ ρ) :
    ∃ t : ℝ, 0 ≤ t ∧ r + ρ * cos (θ + offset d γ ρ) = t * a ∧
      ρ * sin (θ + offset d γ ρ) = h + t * b := by
  let t := travel d (cos (π - γ)) (sin (π - γ)) ρ / d
  have tp : 0 ≤ t := div_nonneg
    (travel_spec C.radius_pos (cos_nonneg_of_mem_Icc
      ⟨by linarith [C.lower, C.upper], by linarith [C.lower, C.upper]⟩)
      (cos_sq_add_sin_sq (π - γ)) outside).1 C.radius_pos.le
  have td : t * d = travel d (cos (π - γ)) (sin (π - γ)) ρ := by
    dsimp [t]; field_simp [ne_of_gt C.radius_pos]
  have position := outer_arm C.radius_pos C.lower C.upper outside θ
  have posx := congrArg (fun z : Plane => z 0) position
  have posy := congrArg (fun z : Plane => z 1) position
  simp only [PiLp.smul_apply, PiLp.add_apply, smul_eq_mul, direction_x, direction_y] at posx posy
  rw [← td] at posx posy
  refine ⟨t, tp, ?_, ?_⟩
  · nlinarith [congrArg (fun x : ℝ => t * x) C.ray_x, C.source_x]
  · nlinarith [congrArg (fun x : ℝ => t * x) C.ray_y, C.source_y]

/-- Exactly one angular location on the upper semicircle can be a zero.
If the predicted angle has passed either end of that semicircle, there is none. -/
theorem zero_iff_boundary_angle {ρ φ : ℝ} (rp : 0 < ρ) (ph : φ ∈ Icc 0 π) :
    level h r a b (r + ρ * cos φ) (ρ * sin φ) = 0 ↔ φ = θ + offset d γ ρ := by
  have vp : 0 ≤ ρ * sin φ := mul_nonneg rp.le (sin_nonneg_of_nonneg_of_le_pi ph.1 ph.2)
  constructor
  · intro zero
    rcases level_zero_on_arm C.height_pos vp C.outward C.ray_nonzero zero with inner | outer
    · have angle := C.inner_zero_angle rp ph inner.2
      have outside : ρ ≤ d := by
        rw [angle, C.source_y] at inner
        by_contra after
        have product := mul_pos (sub_pos.mpr (lt_of_not_ge after))
          (sin_pos_of_pos_of_lt_pi C.angle_pos C.angle_lt_pi)
        linarith [inner.1.2]
      by_cases strict : ρ < d
      · simpa [offset, strict] using angle
      · have same : ρ = d := le_antisymm outside (le_of_not_gt strict)
        rw [same, offset_at_elbow C.radius_pos C.lower C.upper, add_zero]
        exact angle
    · obtain ⟨t, tp, px, py⟩ := outer
      have circle := circle_square (r := r) ρ φ
      rw [px, py] at circle
      obtain ⟨outside, travel_eq⟩ := C.outer_parameter rp tp circle
      have position := outer_arm C.radius_pos C.lower C.upper outside θ
      have posx := congrArg (fun z : Plane => z 0) position
      have posy := congrArg (fun z : Plane => z 1) position
      simp only [PiLp.smul_apply, PiLp.add_apply, smul_eq_mul, direction_x, direction_y] at posx posy
      rw [← travel_eq] at posx posy
      have cosine : cos φ = cos (θ + offset d γ ρ) := by
        nlinarith [congrArg (fun x : ℝ => t * x) C.ray_x, C.source_x]
      have sine : sin φ = sin (θ + offset d γ ρ) := by
        nlinarith [congrArg (fun x : ℝ => t * x) C.ray_y, C.source_y]
      have beta := C.boundary_angle_in_half (by rw [← sine]; exact sin_nonneg_of_nonneg_of_le_pi ph.1 ph.2)
      exact strictAntiOn_cos.injOn ph beta cosine
  · intro angle
    by_cases inside : ρ < d
    · have same : φ = θ := by simpa [offset, inside] using angle
      apply level_zero_of_inner C.height_pos C.outward
      · rw [same, C.source_y]
        exact mul_le_mul_of_nonneg_right inside.le (sin_nonneg_of_nonneg_of_le_pi C.angle_pos.le C.angle_lt_pi.le)
      · rw [same, C.source_y, show r = -(d * cos θ) by linarith [C.source_x]]
        ring
    · have outside : d ≤ ρ := le_of_not_gt inside
      obtain ⟨t, tp, px, py⟩ := C.boundary_ray_point outside
      rw [angle, px, py]
      exact level_zero_of_outer C.height_pos C.outward tp

end ArmCoordinates
end SixVertexUnfolding.Wedge
