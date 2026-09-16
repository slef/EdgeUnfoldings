import SixVertexUnfolding.Geometry.HingeMetricComparison

/-! The hinge distance comparison is strict when the two triangles are not coplanar. -/

namespace SixVertexUnfolding

/-- Equality at the negative Cauchy–Schwarz bound would put y on the line through x. -/
theorem inner_gt_negative_norm_of_not_in_span (x y : Space) (nonzero : x ≠ 0)
    (outside : y ∉ Submodule.span ℝ ({x} : Set Space)) :
    -‖x‖ * ‖y‖ < inner ℝ x y := by
  have lower := (abs_le.mp (abs_real_inner_le_norm x y)).1
  have y_nonzero : y ≠ 0 := by intro zero; exact outside (zero ▸ Submodule.zero_mem _)
  apply lt_of_le_of_ne (by simpa only [neg_mul] using lower)
  intro equal
  have norm_equal : ‖inner ℝ x y‖ = ‖x‖ * ‖y‖ := by
    rw [← equal, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg (norm_nonneg _),
      abs_of_nonneg (norm_nonneg _)]
  obtain ⟨t, _, same⟩ := (norm_inner_eq_norm_iff nonzero y_nonzero).mp norm_equal
  exact outside (Submodule.mem_span_singleton.mpr ⟨t, same.symm⟩)

/-- Noncoplanarity of the hinge and the free vertices survives removal of the hinge components. -/
theorem hingeRemainders_independent (axis x y : Space)
    (x_outside : x ∉ Submodule.span ℝ ({axis} : Set Space))
    (y_outside : y ∉ Submodule.span ℝ ({axis, x} : Set Space)) :
    hingeRemainder axis x ≠ 0 ∧
      hingeRemainder axis y ∉ Submodule.span ℝ ({hingeRemainder axis x} : Set Space) := by
  constructor
  · intro zero
    apply x_outside
    exact Submodule.mem_span_singleton.mpr
      ⟨inner ℝ axis x, (sub_eq_zero.mp zero).symm⟩
  · intro member
    obtain ⟨t, equal⟩ := Submodule.mem_span_singleton.mp member
    let S := Submodule.span ℝ ({axis, x} : Set Space)
    have axis_in : axis ∈ S := Submodule.subset_span (Or.inl rfl)
    have x_in : x ∈ S := Submodule.subset_span (Or.inr rfl)
    have x_remainder_in : hingeRemainder axis x ∈ S :=
      Submodule.sub_mem _ x_in (Submodule.smul_mem _ _ axis_in)
    have y_remainder_in : hingeRemainder axis y ∈ S := equal ▸ S.smul_mem t x_remainder_in
    apply y_outside
    have sum_in := S.add_mem y_remainder_in (S.smul_mem (inner ℝ axis y) axis_in)
    simpa only [hingeRemainder, sub_add_cancel] using sum_in

/-- The unfolded inner product is strictly smaller for a noncoplanar pair of triangles. -/
theorem opposite_flattening_inner_lt (axis : Space) (flat_axis : Plane)
    (axis_unit : ‖axis‖ = 1) (flat_unit : ‖flat_axis‖ = 1)
    (x y : Space) (flat_x flat_y : Plane)
    (x_length : ‖flat_x‖ = ‖x‖) (y_length : ‖flat_y‖ = ‖y‖)
    (x_along : inner ℝ flat_axis flat_x = inner ℝ axis x)
    (y_along : inner ℝ flat_axis flat_y = inner ℝ axis y)
    (opposite : inner ℝ (hingeRemainder flat_axis flat_x)
      (hingeRemainder flat_axis flat_y) ≤ 0)
    (x_outside : x ∉ Submodule.span ℝ ({axis} : Set Space))
    (y_outside : y ∉ Submodule.span ℝ ({axis, x} : Set Space)) :
    inner ℝ flat_x flat_y < inner ℝ x y := by
  have flat_nonzero : flat_axis ≠ 0 := by intro zero; simp [zero] at flat_unit
  have minimum := opposite_perpendicular_inner flat_axis
    (hingeRemainder flat_axis flat_x) (hingeRemainder flat_axis flat_y) flat_nonzero
    (hingeRemainder_orthogonal flat_unit flat_x) (hingeRemainder_orthogonal flat_unit flat_y)
    opposite
  have independent := hingeRemainders_independent axis x y x_outside y_outside
  have strict := inner_gt_negative_norm_of_not_in_span
    (hingeRemainder axis x) (hingeRemainder axis y) independent.1 independent.2
  rw [inner_eq_hinge_components flat_unit, inner_eq_hinge_components axis_unit,
    x_along, y_along, minimum,
    hingeRemainder_norm_eq axis flat_axis axis_unit flat_unit x flat_x x_length x_along,
    hingeRemainder_norm_eq axis flat_axis axis_unit flat_unit y flat_y y_length y_along]
  linarith

end SixVertexUnfolding
