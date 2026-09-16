import SixVertexUnfolding.Geometry.WedgeRotation

/-! A continuous signed function for the Cartesian wedge.
Its nonpositive set is exactly the region already used in the root step.
This lets us compare the Cartesian and polar descriptions on each circle.
-/

namespace SixVertexUnfolding.Wedge

open Set

private theorem product_nonpos {c x : ℝ} (cp : 0 < c) : c * x ≤ 0 ↔ x ≤ 0 := by
  constructor
  · intro bound
    by_contra positive
    exact (not_le_of_gt (mul_pos cp (lt_of_not_ge positive))) bound
  · exact mul_nonpos_of_nonneg_of_nonpos cp.le

private theorem quotient_nonneg {x y : ℝ} (hx : x ≤ 0) (hy : y ≤ 0) : 0 ≤ x / y := by
  simpa using div_nonneg (neg_nonneg.mpr hx) (neg_nonneg.mpr hy)

/-- A signed height: nonpositive means inside the chosen wedge. -/
noncomputable def level (h r a b x v : ℝ) : ℝ :=
  if 0 < b then
    if v ≤ h then b * (h * x - r * (h - v)) else h * (b * x - a * (v - h))
  else if b = 0 then
    if a < 0 then max (v - h) (h * x - r * (h - v))
    else min (h - v) (h * x - r * (h - v))
  else if a < 0 then max (h * x - r * (h - v)) (b * x - a * (v - h))
    else min (h * x - r * (h - v)) (b * x - a * (v - h))

theorem root_pos_of_left_down {h r a b : ℝ} (hp : 0 < h)
    (outward : 0 ≤ h * b - r * a) (al : a < 0) (bd : b < 0) : 0 < r := by
  by_contra hr
  have ra := mul_nonneg_of_nonpos_of_nonpos (le_of_not_gt hr) al.le
  have hb := mul_neg_of_pos_of_neg hp bd
  linarith

theorem root_neg_of_right_down {h r a b : ℝ} (hp : 0 < h)
    (outward : 0 ≤ h * b - r * a) (ar : 0 ≤ a) (bd : b < 0) : r < 0 ∧ 0 < a := by
  have hb := mul_neg_of_pos_of_neg hp bd
  have ap : 0 < a := by
    by_contra ha
    have az := le_antisymm (le_of_not_gt ha) ar
    rw [az, mul_zero, sub_zero] at outward
    linarith
  refine ⟨?_, ap⟩
  by_contra hr
  have ra := mul_nonneg (le_of_not_gt hr) ap.le
  linarith

private theorem bounded_height {h r a b x v : ℝ} (hp : 0 < h) (rp : 0 < r)
    (al : a < 0) (bd : b < 0) (inner : h * x ≤ r * (h - v))
    (outer : b * x ≤ a * (v - h)) : v ≤ h := by
  by_contra hv
  have height := lt_of_not_ge hv
  have ir := mul_neg_of_pos_of_neg rp (sub_neg.mpr height)
  have xn : x < 0 := by nlinarith
  have bo := mul_pos_of_neg_of_neg bd xn
  have ao := mul_neg_of_neg_of_pos al (sub_pos.mpr height)
  linarith

private theorem complement_height {h r a b x v : ℝ} (hp : 0 < h) (rn : r < 0)
    (ar : 0 < a) (bd : b < 0) (inner : r * (h - v) ≤ h * x)
    (outer : a * (v - h) ≤ b * x) : v ≤ h := by
  by_contra hv
  have height := lt_of_not_ge hv
  have ir := mul_pos_of_neg_of_neg rn (sub_neg.mpr height)
  have xp : 0 < x := by nlinarith
  have bo := mul_neg_of_neg_of_pos bd xp
  have ao := mul_pos ar (sub_pos.mpr height)
  linarith

/-- The signed description is exactly the existing Cartesian region. -/
theorem mem_region_iff_level {h r a b : ℝ} (hp : 0 < h)
    (outward : 0 ≤ h * b - r * a) (ray : a ≠ 0 ∨ b ≠ 0) (z : Plane) :
    z ∈ region h r a b ↔ level h r a b (z 0) |z 1| ≤ 0 := by
  by_cases bu : 0 < b
  · by_cases low : |z 1| < h
    · have hb := not_le_of_gt low
      simp [region, level, bu, bu.le, low.le, hb,
        product_nonpos bu]
    · by_cases equal : |z 1| = h
      · simp only [region, mem_setOf_eq, level, bu, if_true, equal, le_refl,
          sub_self, mul_zero, sub_zero, true_and]
        rw [if_pos bu.le]
        constructor
        · rintro (outer | inner)
          · have xn : z 0 ≤ 0 := (product_nonpos bu).mp outer
            exact mul_nonpos_of_nonneg_of_nonpos bu.le (mul_nonpos_of_nonneg_of_nonpos hp.le xn)
          · exact mul_nonpos_of_nonneg_of_nonpos bu.le inner
        · intro member
          exact Or.inr ((product_nonpos bu).mp member)
      · have high : h < |z 1| := lt_of_le_of_ne (le_of_not_gt low) (Ne.symm equal)
        simp [region, level, bu, bu.le, high.le, not_le_of_gt high,
          product_nonpos hp]
  · by_cases bz : b = 0
    · have an : a ≠ 0 := ray.resolve_right (not_not_intro bz)
      by_cases al : a < 0
      · simp [region, level, bz, al, not_lt_of_ge al.le]
      · have ap : 0 < a := lt_of_le_of_ne (le_of_not_gt al) (Ne.symm an)
        simp only [region, mem_setOf_eq, level, bz, lt_self_iff_false, if_false,
          le_refl, if_true, al, ap, and_true, min_le_iff, sub_nonpos]
        constructor
        · rintro (above | ⟨_, inside⟩)
          · exact Or.inl above
          · exact Or.inr inside
        · rintro (above | inside)
          · exact Or.inl above
          · exact (le_total h |z 1|).elim Or.inl (fun below => Or.inr ⟨below, inside⟩)
    · have bd : b < 0 := lt_of_le_of_ne (le_of_not_gt bu) bz
      by_cases al : a < 0
      · have rp := root_pos_of_left_down hp outward al bd
        simp only [region, mem_setOf_eq, level, bu, if_false, bz, al, if_true,
          not_le_of_gt bd, not_lt_of_ge al.le, and_false, false_or, max_le_iff, sub_nonpos]
        constructor
        · exact fun member => member.2
        · intro member
          exact ⟨bounded_height hp rp al bd member.1 member.2, member⟩
      · obtain ⟨rn, ap⟩ := root_neg_of_right_down hp outward (le_of_not_gt al) bd
        simp only [region, mem_setOf_eq, level, bu, if_false, bz, al,
          not_le_of_gt bd, ap, and_true, min_le_iff, sub_nonpos]
        constructor
        · rintro (above | ⟨_, inside⟩)
          · by_contra missing
            push Not at missing
            have bound := complement_height hp rn ap bd missing.1.le missing.2.le
            have equal := le_antisymm bound above
            rw [equal, sub_self, mul_zero] at missing
            have xp : 0 < z 0 := by nlinarith [missing.1]
            have := mul_neg_of_neg_of_pos bd xp
            linarith [missing.2]
          · exact inside
        · intro inside
          exact (le_total h |z 1|).elim Or.inl (fun below => Or.inr ⟨below, inside⟩)

/-- The two pieces agree at the source-image height, so no artificial
discontinuity is introduced by the case distinction. -/
theorem continuous_level_coordinates (h r a b : ℝ) :
    Continuous (fun z : ℝ × ℝ => level h r a b z.1 z.2) := by
  have cx : Continuous (fun z : ℝ × ℝ => z.1) := continuous_fst
  have cv : Continuous (fun z : ℝ × ℝ => z.2) := continuous_snd
  have ci : Continuous (fun z : ℝ × ℝ => h * z.1 - r * (h - z.2)) :=
    (continuous_const.mul cx).sub (continuous_const.mul (continuous_const.sub cv))
  have co : Continuous (fun z : ℝ × ℝ => b * z.1 - a * (z.2 - h)) :=
    (continuous_const.mul cx).sub (continuous_const.mul (cv.sub continuous_const))
  unfold level
  split_ifs with bu bz al al
  · exact (continuous_const.mul ci).if_le (continuous_const.mul co) cv continuous_const
      (fun z same => by dsimp; rw [same]; ring)
  · exact (cv.sub continuous_const).max ci
  · exact (continuous_const.sub cv).min ci
  · exact ci.max co
  · exact ci.min co

theorem continuous_level (h r a b : ℝ) :
    Continuous (fun z : Plane => level h r a b (z 0) |z 1|) :=
  (continuous_level_coordinates h r a b).comp
    ((EuclideanSpace.proj 0).continuous.prodMk (EuclideanSpace.proj 1).continuous.abs)

private theorem ray_of_line {a b x v h : ℝ} (bn : b ≠ 0)
    (positive : 0 ≤ (v - h) / b) (line : b * x = a * (v - h)) :
    ∃ t : ℝ, 0 ≤ t ∧ x = t * a ∧ v = h + t * b := by
  refine ⟨(v - h) / b, positive, ?_, ?_⟩
  · field_simp
    nlinarith
  · field_simp
    ring

/-- On the upper half-plane, a zero lies on an actual inner segment or
on an actual forward outer ray. The horizontal joins add no extra zeros. -/
theorem level_zero_on_arm {h r a b x v : ℝ} (hp : 0 < h) (vp : 0 ≤ v)
    (outward : 0 ≤ h * b - r * a) (ray : a ≠ 0 ∨ b ≠ 0)
    (zero : level h r a b x v = 0) :
    (v ∈ Icc 0 h ∧ h * x = r * (h - v)) ∨
      ∃ t : ℝ, 0 ≤ t ∧ x = t * a ∧ v = h + t * b := by
  by_cases bu : 0 < b
  · by_cases low : v ≤ h
    · simp only [level, bu, if_true, low] at zero
      have inner := (mul_eq_zero.mp zero).resolve_left (ne_of_gt bu)
      exact Or.inl ⟨⟨vp, low⟩, sub_eq_zero.mp inner⟩
    · simp only [level, bu, if_true, low, if_false] at zero
      have outer := (mul_eq_zero.mp zero).resolve_left (ne_of_gt hp)
      exact Or.inr (ray_of_line (ne_of_gt bu)
        (div_nonneg (sub_nonneg.mpr (le_of_not_ge low)) bu.le) (sub_eq_zero.mp outer))
  · by_cases bz : b = 0
    · have an := ray.resolve_right (not_not_intro bz)
      by_cases al : a < 0
      · simp only [level, bz, lt_self_iff_false, if_false, if_true, al] at zero
        have bounds := max_le_iff.mp zero.le
        rcases max_eq_iff.mp zero with ⟨height, _⟩ | ⟨inner, _⟩
        · have vh : v = h := sub_eq_zero.mp height
          have xn : x ≤ 0 := by rw [vh] at bounds; nlinarith [bounds.2]
          refine Or.inr ⟨x / a, quotient_nonneg xn al.le, ?_, ?_⟩
          · field_simp
          · simp [bz, vh]
        · exact Or.inl ⟨⟨vp, sub_nonpos.mp bounds.1⟩, sub_eq_zero.mp inner⟩
      · have ap : 0 < a := lt_of_le_of_ne (le_of_not_gt al) (Ne.symm an)
        simp only [level, bz, lt_self_iff_false, if_false, if_true, al] at zero
        have bounds := le_min_iff.mp zero.ge
        rcases min_eq_iff.mp zero with ⟨height, _⟩ | ⟨inner, _⟩
        · have vh : v = h := (sub_eq_zero.mp height).symm
          have xp : 0 ≤ x := by rw [vh] at bounds; nlinarith [bounds.2]
          refine Or.inr ⟨x / a, div_nonneg xp ap.le, ?_, ?_⟩
          · field_simp
          · simp [bz, vh]
        · exact Or.inl ⟨⟨vp, sub_nonneg.mp bounds.1⟩, sub_eq_zero.mp inner⟩
    · have bd : b < 0 := lt_of_le_of_ne (le_of_not_gt bu) bz
      by_cases al : a < 0
      · have rp := root_pos_of_left_down hp outward al bd
        simp only [level, bu, if_false, bz, al, if_true] at zero
        have bounds := max_le_iff.mp zero.le
        have height := bounded_height hp rp al bd (sub_nonpos.mp bounds.1) (sub_nonpos.mp bounds.2)
        rcases max_eq_iff.mp zero with ⟨inner, _⟩ | ⟨outer, _⟩
        · exact Or.inl ⟨⟨vp, height⟩, sub_eq_zero.mp inner⟩
        · exact Or.inr (ray_of_line bz
            (quotient_nonneg (sub_nonpos.mpr height) bd.le) (sub_eq_zero.mp outer))
      · obtain ⟨rn, ap⟩ := root_neg_of_right_down hp outward (le_of_not_gt al) bd
        simp only [level, bu, if_false, bz, al] at zero
        have bounds := le_min_iff.mp zero.ge
        have height := complement_height hp rn ap bd (sub_nonneg.mp bounds.1) (sub_nonneg.mp bounds.2)
        rcases min_eq_iff.mp zero with ⟨inner, _⟩ | ⟨outer, _⟩
        · exact Or.inl ⟨⟨vp, height⟩, sub_eq_zero.mp inner⟩
        · exact Or.inr (ray_of_line bz
            (quotient_nonneg (sub_nonpos.mpr height) bd.le) (sub_eq_zero.mp outer))

/-- Every point of the upper inner segment is a zero of the signed function. -/
theorem level_zero_of_inner {h r a b x v : ℝ} (hp : 0 < h)
    (outward : 0 ≤ h * b - r * a) (low : v ≤ h)
    (inner : h * x = r * (h - v)) : level h r a b x v = 0 := by
  have iz : h * x - r * (h - v) = 0 := sub_eq_zero.mpr inner
  by_cases bu : 0 < b
  · simp [level, bu, low, iz]
  · by_cases bz : b = 0
    · by_cases al : a < 0
      · simp [level, bz, al, iz, max_eq_right (sub_nonpos.mpr low)]
      · simp [level, bz, al, iz, min_eq_right (sub_nonneg.mpr low)]
    · have bd : b < 0 := lt_of_le_of_ne (le_of_not_gt bu) bz
      have identity : h * (b * x - a * (v - h)) = (h - v) * (r * b + h * a) := by
        nlinarith [congrArg (fun t : ℝ => b * t) inner]
      by_cases al : a < 0
      · have rp := root_pos_of_left_down hp outward al bd
        have sign : r * b + h * a ≤ 0 := add_nonpos
          (mul_nonpos_of_nonneg_of_nonpos rp.le bd.le) (mul_nonpos_of_nonneg_of_nonpos hp.le al.le)
        have product := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr low) sign
        have bound : b * x - a * (v - h) ≤ 0 := (product_nonpos hp).mp (by linarith)
        simp [level, bu, bz, al, iz, max_eq_left bound]
      · obtain ⟨rn, ap⟩ := root_neg_of_right_down hp outward (le_of_not_gt al) bd
        have sign : 0 ≤ r * b + h * a := add_nonneg
          (mul_nonneg_of_nonpos_of_nonpos rn.le bd.le) (mul_nonneg hp.le ap.le)
        have product := mul_nonneg (sub_nonneg.mpr low) sign
        have bound : 0 ≤ b * x - a * (v - h) := by nlinarith
        simp [level, bu, bz, al, iz, min_eq_left bound]

/-- Every point of the forward upper ray, before it crosses the axis,
is a zero. This also includes horizontal and tangent outer rays. -/
theorem level_zero_of_outer {h r a b t : ℝ} (hp : 0 < h)
    (outward : 0 ≤ h * b - r * a) (tp : 0 ≤ t) :
    level h r a b (t * a) (h + t * b) = 0 := by
  have oz : b * (t * a) - a * ((h + t * b) - h) = 0 := by ring
  have identity : h * (t * a) - r * (h - (h + t * b)) = t * (h * a + r * b) := by ring
  by_cases bu : 0 < b
  · by_cases low : h + t * b ≤ h
    · have tz : t = 0 := by nlinarith
      simp [level, bu, tz]
    · simp only [level, bu, if_true, low, if_false, oz, mul_zero]
  · by_cases bz : b = 0
    · by_cases al : a < 0
      · have sign : h * (t * a) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hp.le
          (mul_nonpos_of_nonneg_of_nonpos tp al.le)
        simpa [level, bu, bz, al] using max_eq_left sign
      · have sign : 0 ≤ h * (t * a) := mul_nonneg hp.le (mul_nonneg tp (le_of_not_gt al))
        simpa [level, bu, bz, al] using min_eq_left sign
    · have bd : b < 0 := lt_of_le_of_ne (le_of_not_gt bu) bz
      by_cases al : a < 0
      · have rp := root_pos_of_left_down hp outward al bd
        have sign : h * a + r * b ≤ 0 := add_nonpos
          (mul_nonpos_of_nonneg_of_nonpos hp.le al.le) (mul_nonpos_of_nonneg_of_nonpos rp.le bd.le)
        have bound := mul_nonpos_of_nonneg_of_nonpos tp sign
        simp only [level, bu, if_false, bz, al, if_true, oz, identity]
        exact max_eq_right bound
      · obtain ⟨rn, ap⟩ := root_neg_of_right_down hp outward (le_of_not_gt al) bd
        have sign : 0 ≤ h * a + r * b := add_nonneg
          (mul_nonneg hp.le ap.le) (mul_nonneg_of_nonpos_of_nonpos rn.le bd.le)
        have bound := mul_nonneg tp sign
        simp only [level, bu, if_false, bz, al, oz, identity]
        exact min_eq_right bound

end SixVertexUnfolding.Wedge
