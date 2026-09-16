import SixVertexUnfolding.Geometry.WedgeCircleZeros

/-! The boundary angle determines which side of a circle lies in the wedge.
The intermediate value theorem propagates the two axis signs between zeros.
-/

namespace SixVertexUnfolding.Wedge

open Real Set

private theorem sign_from_unique_zero {f : ℝ → ℝ} {β : ℝ} (continuous : Continuous f)
    (zeros : ∀ φ ∈ Icc (0 : ℝ) π, f φ = 0 ↔ φ = β)
    (start : 0 < β → 0 < f 0) (finish : β < π → f π < 0)
    {φ : ℝ} (ph : φ ∈ Icc 0 π) : f φ ≤ 0 ↔ β ≤ φ := by
  constructor
  · intro inside
    by_contra before
    have after : φ < β := lt_of_not_ge before
    have positive := start (lt_of_le_of_lt ph.1 after)
    obtain ⟨c, bounds, zero⟩ := intermediate_value_Icc' ph.1 continuous.continuousOn
      (show (0 : ℝ) ∈ Icc (f φ) (f 0) from ⟨inside, positive.le⟩)
    have same := (zeros c ⟨bounds.1, bounds.2.trans ph.2⟩).mp zero
    linarith [bounds.2]
  · intro after
    by_cases equal : φ = β
    · exact ((zeros φ ph).mpr equal).le
    · have strict : β < φ := lt_of_le_of_ne after (Ne.symm equal)
      have negative := finish (strict.trans_le ph.2)
      by_contra outside
      have positive := lt_of_not_ge outside
      obtain ⟨c, bounds, zero⟩ := intermediate_value_Icc' ph.2 continuous.continuousOn
        (show (0 : ℝ) ∈ Icc (f π) (f φ) from ⟨negative.le, positive.le⟩)
      have same := (zeros c ⟨ph.1.trans bounds.1, bounds.2⟩).mp zero
      linarith [bounds.1]

namespace ArmCoordinates

variable {h r a b d θ γ : ℝ} (C : ArmCoordinates h r a b d θ γ)
include C

omit C in
private theorem offset_bounds (ρ : ℝ) : offset d γ ρ ∈ Icc (-(π / 2)) (π / 2) := by
  unfold offset
  split_ifs
  · constructor <;> linarith [pi_pos]
  · exact arcsin_mem_Icc _

private theorem boundary_positive_of_root_positive {ρ : ℝ} (rp : 0 < r) :
    0 < θ + offset d γ ρ := by
  have angle : π / 2 < θ := by
    by_contra before
    have cosine := cos_nonneg_of_mem_Icc
      ⟨by linarith [C.angle_pos, pi_pos], le_of_not_gt before⟩
    have product := mul_nonneg C.radius_pos.le cosine
    linarith [C.source_x]
  linarith [(offset_bounds (d := d) (γ := γ) ρ).1]

private theorem boundary_before_pi_of_root_negative {ρ : ℝ} (rn : r < 0) :
    θ + offset d γ ρ < π := by
  have angle : θ < π / 2 := by
    by_contra after
    have cosine := cos_nonpos_of_pi_div_two_le_of_le (le_of_not_gt after)
      (by linarith [C.angle_lt_pi, pi_pos])
    have product := mul_nonpos_of_nonneg_of_nonpos C.radius_pos.le cosine
    linarith [C.source_x]
  linarith [(offset_bounds (d := d) (γ := γ) ρ).2]

/-- Before an outer ray reaches the axis, its distance from the root is
strictly less than the distance to its axis intersection. -/
private theorem radius_before_axis {ρ t : ℝ} (rp : 0 < ρ) (bd : b < 0)
    (tp : 0 ≤ t) (above : 0 < h + t * b)
    (circle : (t * a - r) ^ 2 + (h + t * b) ^ 2 = ρ ^ 2) :
    ρ < |(-h / b) * a - r| := by
  let T := -h / b
  have Tb : T * b = -h := by dsimp [T]; field_simp [ne_of_lt bd]
  have order : t < T := by
    by_contra reversed
    have product := mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (le_of_not_gt reversed)) bd.le
    nlinarith
  have Tpos : 0 < T := lt_of_le_of_lt tp order
  have ray := C.ray_square
  have w := C.outward
  have increase := mul_pos (sub_pos.mpr order)
    (show 0 < 2 * (h * b - r * a) + (T + t) * d ^ 2 by
      have product := mul_pos (by linarith : 0 < T + t) (sq_pos_of_pos C.radius_pos)
      linarith)
  have farther : ρ ^ 2 < (T * a - r) ^ 2 := by
    nlinarith [congrArg (fun x : ℝ => T ^ 2 * x) ray,
      congrArg (fun x : ℝ => t ^ 2 * x) ray,
      congrArg (fun x : ℝ => x ^ 2) Tb]
  change ρ < |T * a - r|
  nlinarith [sq_abs (T * a - r), abs_nonneg (T * a - r)]

private theorem active_circle_before_axis {ρ : ℝ} (rp : 0 < ρ) (bd : b < 0)
    (active : θ + offset d γ ρ ∈ Ioo 0 π) : ρ < |(-h / b) * a - r| := by
  by_cases inner : ρ < d
  · have cap := C.radius_before_axis C.radius_pos bd (le_refl 0)
      (by simpa using C.height_pos) (by simpa using C.source_square)
    exact inner.trans cap
  · obtain ⟨t, tp, px, py⟩ := C.boundary_ray_point (le_of_not_gt inner)
    have circle := circle_square (r := r) ρ (θ + offset d γ ρ)
    rw [px, py] at circle
    apply C.radius_before_axis rp bd tp _ circle
    rw [← py]
    exact mul_pos rp (sin_pos_of_pos_of_lt_pi active.1 active.2)

private theorem right_level_positive {ρ : ℝ} (rp : 0 < ρ)
    (extra : b < 0 → 0 ≤ a → 0 < b * (r + ρ) + a * h) :
    0 < level h r a b (r + ρ) 0 := by
  have hp := C.height_pos
  have inner : h * (r + ρ) - r * h = h * ρ := by ring
  have positive := mul_pos hp rp
  by_cases bu : 0 < b
  · simpa [level, bu, hp.le, inner] using mul_pos bu positive
  · by_cases bz : b = 0
    · by_cases al : a < 0
      · simp only [level, bz, lt_self_iff_false, if_false, if_true, al, sub_zero, zero_sub, inner]
        exact lt_of_lt_of_le positive (le_max_right _ _)
      · simp only [level, bz, lt_self_iff_false, if_false, if_true, al, sub_zero, inner]
        exact lt_min hp positive
    · have bd : b < 0 := lt_of_le_of_ne (le_of_not_gt bu) bz
      by_cases al : a < 0
      · simp only [level, bu, if_false, bz, al, if_true, sub_zero, inner]
        exact lt_of_lt_of_le positive (le_max_left _ _)
      · simp only [level, bu, if_false, bz, al, sub_zero, zero_sub, mul_neg, sub_neg_eq_add, inner]
        exact lt_min positive (extra bd (le_of_not_gt al))

private theorem left_level_negative {ρ : ℝ} (rp : 0 < ρ)
    (extra : b < 0 → a < 0 → b * (r - ρ) + a * h < 0) :
    level h r a b (r - ρ) 0 < 0 := by
  have hp := C.height_pos
  have inner : h * (r - ρ) - r * h = -(h * ρ) := by ring
  have negative := neg_neg_of_pos (mul_pos hp rp)
  by_cases bu : 0 < b
  · simpa [level, bu, hp.le, inner] using mul_neg_of_pos_of_neg bu negative
  · by_cases bz : b = 0
    · by_cases al : a < 0
      · simp only [level, bz, lt_self_iff_false, if_false, if_true, al, sub_zero, zero_sub, inner]
        exact max_lt (neg_neg_of_pos hp) negative
      · simp only [level, bz, lt_self_iff_false, if_false, if_true, al, sub_zero, inner]
        exact lt_of_le_of_lt (min_le_right _ _) negative
    · have bd : b < 0 := lt_of_le_of_ne (le_of_not_gt bu) bz
      by_cases al : a < 0
      · simp only [level, bu, if_false, bz, al, if_true, sub_zero, zero_sub, mul_neg, sub_neg_eq_add, inner]
        exact max_lt negative (extra bd al)
      · simp only [level, bu, if_false, bz, al, sub_zero, inner]
        exact lt_of_le_of_lt (min_le_left _ _) negative

private theorem start_positive {ρ : ℝ} (rp : 0 < ρ) (before : 0 < θ + offset d γ ρ) :
    0 < level h r a b (r + ρ) 0 := by
  apply C.right_level_positive rp
  intro bd ar
  obtain ⟨rn, ap⟩ := root_neg_of_right_down C.height_pos C.outward ar bd
  have cap := C.active_circle_before_axis rp bd ⟨before, C.boundary_before_pi_of_root_negative rn⟩
  let T := -h / b
  have Tb : T * b = -h := by dsimp [T]; field_simp [ne_of_lt bd]
  have Tpos : 0 < T := by
    by_contra ht
    have := mul_nonneg_of_nonpos_of_nonpos (le_of_not_gt ht) bd.le
    nlinarith [C.height_pos]
  have axis_positive : 0 < T * a - r := by nlinarith [mul_pos Tpos ap]
  change ρ < |T * a - r| at cap
  rw [abs_of_pos axis_positive] at cap
  have product := mul_pos_of_neg_of_neg bd (show r + ρ - T * a < 0 by linarith)
  nlinarith [congrArg (fun x : ℝ => a * x) Tb]

private theorem finish_negative {ρ : ℝ} (rp : 0 < ρ) (before : θ + offset d γ ρ < π) :
    level h r a b (r - ρ) 0 < 0 := by
  apply C.left_level_negative rp
  intro bd al
  have rr := root_pos_of_left_down C.height_pos C.outward al bd
  have cap := C.active_circle_before_axis rp bd ⟨C.boundary_positive_of_root_positive rr, before⟩
  let T := -h / b
  have Tb : T * b = -h := by dsimp [T]; field_simp [ne_of_lt bd]
  have Tpos : 0 < T := by
    by_contra ht
    have := mul_nonneg_of_nonpos_of_nonpos (le_of_not_gt ht) bd.le
    nlinarith [C.height_pos]
  have axis_negative : T * a - r < 0 := by nlinarith [mul_neg_of_pos_of_neg Tpos al]
  change ρ < |T * a - r| at cap
  rw [abs_of_neg axis_negative] at cap
  have product := mul_neg_of_neg_of_pos bd (show 0 < r - ρ - T * a by linarith)
  nlinarith [congrArg (fun x : ℝ => a * x) Tb]

/-- On every upper semicircle, the Cartesian wedge contains exactly the
arc starting at the polar boundary angle. Empty and full arcs are included. -/
theorem circle_sign {ρ φ : ℝ} (rp : 0 < ρ) (ph : φ ∈ Icc 0 π) :
    level h r a b (r + ρ * cos φ) (ρ * sin φ) ≤ 0 ↔ θ + offset d γ ρ ≤ φ := by
  apply sign_from_unique_zero
    ((continuous_level_coordinates h r a b).comp
      ((continuous_const.add (continuous_const.mul continuous_cos)).prodMk
        (continuous_const.mul continuous_sin)))
    (fun ψ bounds => C.zero_iff_boundary_angle rp bounds) _ _ ph
  · intro before
    simpa using C.start_positive rp before
  · intro before
    simpa using C.finish_negative rp before

end ArmCoordinates
end SixVertexUnfolding.Wedge
