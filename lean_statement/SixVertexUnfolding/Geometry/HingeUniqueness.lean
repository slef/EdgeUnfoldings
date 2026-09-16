import SixVertexUnfolding.Geometry.HingeSides

/-! A third planar vertex is determined by its distances to a hinge and its side of the hinge. -/

namespace SixVertexUnfolding

/-- Equal distances to two fixed points give equal components along their hinge. -/
theorem equal_hinge_component (a b x y : Plane)
    (at_a : dist a x = dist a y) (at_b : dist b x = dist b y) :
    inner ℝ (NormedSpace.normalize (b - a)) (x - a) =
      inner ℝ (NormedSpace.normalize (b - a)) (y - a) := by
  have x_norm : ‖x - a‖ = ‖y - a‖ := by simpa only [dist_eq_norm, norm_sub_rev] using at_a
  have b_norm : ‖b - x‖ = ‖b - y‖ := by simpa only [dist_eq_norm] using at_b
  have first := norm_sub_sq_real (b - a) (x - a)
  have second := norm_sub_sq_real (b - a) (y - a)
  simp only [sub_sub_sub_cancel_right, x_norm, b_norm] at first second
  have equal : inner ℝ (b - a) (x - a) = inner ℝ (b - a) (y - a) := by linarith
  simp only [NormedSpace.normalize, real_inner_smul_left, equal]

/-- On the same closed side, matching hinge distances determine the point uniquely. -/
theorem point_eq_of_hinge_distances (a b x y : Plane) (ab : a ≠ b)
    (at_a : dist a x = dist a y) (at_b : dist b x = dist b y)
    (same_side : 0 ≤ inner ℝ (hingeSideVector a b x) (hingeSideVector a b y)) : x = y := by
  let axis := NormedSpace.normalize (b - a)
  have unit : ‖axis‖ = 1 := NormedSpace.norm_normalize (sub_ne_zero.mpr ab.symm)
  have axis_ne : axis ≠ 0 := by intro zero; simp [zero] at unit
  let X := hingeRemainder axis (x - a)
  let Y := hingeRemainder axis (y - a)
  have along : inner ℝ axis (x - a) = inner ℝ axis (y - a) := equal_hinge_component a b x y at_a at_b
  have length : ‖x - a‖ = ‖y - a‖ := by simpa only [dist_eq_norm, norm_sub_rev] using at_a
  have transverse_length : ‖X‖ = ‖Y‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [hingeRemainder_norm_sq unit, hingeRemainder_norm_sq unit, along, length]
  have inner_eq : inner ℝ X Y = ‖X‖ * ‖Y‖ := by
    have minimum := opposite_perpendicular_inner axis X (-Y) axis_ne
      (hingeRemainder_orthogonal unit (x - a))
      (by rw [inner_neg_right, hingeRemainder_orthogonal unit (y - a), neg_zero])
      (by rw [inner_neg_right]; exact neg_nonpos.mpr same_side)
    rw [inner_neg_right, norm_neg] at minimum
    linarith
  have same : X = Y := by
    have square : ‖X - Y‖ ^ 2 = 0 := by
      rw [norm_sub_sq_real, inner_eq, transverse_length]
      ring
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp square))
  change (x - a) - inner ℝ axis (x - a) • axis = (y - a) - inner ℝ axis (y - a) • axis at same
  rw [along] at same
  have recovered := congrArg (fun z : Plane => z + inner ℝ axis (y - a) • axis + a) same
  simpa only [sub_add_cancel] using recovered

/-- Reflecting the reference vertex across the hinge point reverses its hinge-side vector. -/
theorem hingeSideVector_point_reflection (a b x : Plane) :
    hingeSideVector a b (2 • a - x) = -hingeSideVector a b x := by
  have difference : 2 • a - x - a = -(x - a) := by module
  simp only [hingeSideVector, difference, hingeRemainder, inner_neg_right, neg_smul]
  module

end SixVertexUnfolding
