import SixVertexUnfolding.Geometry.PlanarDirections

/-! The explicit slit-edge separator in the local nonoverlap argument. -/

namespace SixVertexUnfolding.SlitSeparator

open Real

/-- The two slit copies are separated by this exact half-angle identity. -/
theorem slit_height_identity (r gap reflex : ℝ) :
    det (direction (-reflex)) (r • direction (-gap) - r • direction 0) =
      -2 * r * sin (gap / 2) * cos (reflex - gap / 2) := by
  rw [det_sub_right, det_smul_right, det_smul_right, direction_det, direction_det]
  have first : -gap - -reflex = reflex - gap := by ring
  have second : 0 - -reflex = reflex := by ring
  rw [first, second, ← mul_sub, sin_sub_sin]
  have average : (reflex - gap + reflex) / 2 = reflex - gap / 2 := by ring
  have difference : (reflex - gap - reflex) / 2 = -(gap / 2) := by ring
  rw [average, difference, sin_neg]
  ring

variable {r gap slit reflex : ℝ}

/-- The closed curvature threshold still gives strict separation of the other slit copy. -/
theorem slit_height_negative (r_pos : 0 < r) (gap_pos : 0 < gap) (_slit_pos : 0 < slit)
    (threshold : π ≤ 2 * slit + gap) (crosses_gap : gap < reflex) (corner : reflex < π - slit) :
    det (direction (-reflex)) (r • direction (-gap) - r • direction 0) < 0 := by
  rw [slit_height_identity]
  have sine : 0 < sin (gap / 2) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have cosine : 0 < cos (reflex - gap / 2) := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have positive := mul_pos (mul_pos r_pos sine) cosine
  nlinarith

/-- The fan pole lies on the same strict side of the slit-edge separator. -/
theorem pole_height_negative (r_pos : 0 < r) (gap_pos : 0 < gap) (slit_pos : 0 < slit)
    (crosses_gap : gap < reflex) (corner : reflex < π - slit) :
    det (direction (-reflex)) (0 - r • direction 0) < 0 := by
  have sine : 0 < sin reflex := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  simp only [det, PiLp.sub_apply, PiLp.zero_apply, PiLp.smul_apply, direction_x, direction_y,
    cos_zero, sin_zero, cos_neg, sin_neg, smul_eq_mul]
  nlinarith [mul_pos r_pos sine]

/-- Both boundary directions of the opposite patch point strictly to the right of the separator. -/
theorem opposite_directions_negative (gap_pos : 0 < gap) (slit_pos : 0 < slit)
    (crosses_gap : gap < reflex) (corner : reflex < π - slit) :
    det (direction (-reflex)) (direction (-π - gap)) < 0 ∧
    det (direction (-reflex)) (direction (-reflex - slit - gap)) < 0 := by
  rw [direction_det, direction_det]
  constructor <;> apply sin_neg_of_neg_of_neg_pi_lt <;> linarith

/-- The closed cone containing the opposite patch, based at the other slit copy. -/
def oppositeCone (r gap slit reflex : ℝ) : Set Plane :=
  {x | ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧
    x = r • direction (-gap) + s • direction (-π - gap) + t • direction (-reflex - slit - gap)}

/-- Every point of that cone stays strictly beyond the slit-edge separator. -/
theorem opposite_cone_height_negative (r_pos : 0 < r) (gap_pos : 0 < gap) (slit_pos : 0 < slit)
    (threshold : π ≤ 2 * slit + gap) (crosses_gap : gap < reflex) (corner : reflex < π - slit)
    {x : Plane} (member : x ∈ oppositeCone r gap slit reflex) :
    det (direction (-reflex)) (x - r • direction 0) < 0 := by
  obtain ⟨s, t, hs, ht, rfl⟩ := member
  have base := slit_height_negative r_pos gap_pos slit_pos threshold crosses_gap corner
  obtain ⟨left, right⟩ := opposite_directions_negative gap_pos slit_pos crosses_gap corner
  simp only [det_sub_right, det_add_right, det_smul_right] at base ⊢
  linarith [mul_nonpos_of_nonneg_of_nonpos hs left.le, mul_nonpos_of_nonneg_of_nonpos ht right.le]

/-- The entire finite opposite slit segment has strict negative height, including its endpoints. -/
theorem finite_slit_height_negative (r_pos : 0 < r) (gap_pos : 0 < gap) (slit_pos : 0 < slit)
    (threshold : π ≤ 2 * slit + gap) (crosses_gap : gap < reflex) (corner : reflex < π - slit)
    {x : Plane} (member : x ∈ segment ℝ 0 (r • direction (-gap))) :
    det (direction (-reflex)) (x - r • direction 0) < 0 := by
  have pole := pole_height_negative r_pos gap_pos slit_pos crosses_gap corner
  have copy := slit_height_negative r_pos gap_pos slit_pos threshold crosses_gap corner
  let height := detHeight (direction (-reflex))
  have convex : Convex ℝ {z | height z < height (r • direction 0)} :=
    (convex_Iio _).linear_preimage height.toLinearMap
  have in_halfplane := convex.segment_subset
    (by simpa only [height, detHeight_apply, det_sub_right, sub_neg] using pole)
    (by simpa only [height, detHeight_apply, det_sub_right, sub_neg] using copy) member
  simpa only [height, detHeight_apply, det_sub_right, sub_neg] using in_halfplane

/-- A petal on the left misses both the opposite patch cone and the entire finite opposite slit. -/
theorem separates_patch_and_slit (r_pos : 0 < r) (gap_pos : 0 < gap) (slit_pos : 0 < slit)
    (threshold : π ≤ 2 * slit + gap) (crosses_gap : gap < reflex) (corner : reflex < π - slit)
    (petal : Set Plane) (left : ∀ x ∈ petal, 0 ≤ det (direction (-reflex)) (x - r • direction 0)) :
    Disjoint petal (oppositeCone r gap slit reflex) ∧ Disjoint petal (segment ℝ 0 (r • direction (-gap))) := by
  constructor
  · apply Set.disjoint_left.mpr
    intro x hx other
    exact (not_lt_of_ge (left x hx))
      (opposite_cone_height_negative r_pos gap_pos slit_pos threshold crosses_gap corner other)
  · apply Set.disjoint_left.mpr
    intro x hx other
    exact (not_lt_of_ge (left x hx))
      (finite_slit_height_negative r_pos gap_pos slit_pos threshold crosses_gap corner other)

end SixVertexUnfolding.SlitSeparator
