import SixVertexUnfolding.Definitions

/-! Resolve vectors into their component along a unit hinge and their perpendicular remainder. -/

namespace SixVertexUnfolding

section Remainders

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def hingeRemainder (axis x : E) : E := x - inner ℝ axis x • axis

theorem hingeRemainder_orthogonal {axis : E} (unit : ‖axis‖ = 1) (x : E) :
    inner ℝ axis (hingeRemainder axis x) = 0 := by
  simp [hingeRemainder, inner_sub_right, inner_smul_right, unit]

theorem hingeRemainder_norm_sq {axis : E} (unit : ‖axis‖ = 1) (x : E) :
    ‖hingeRemainder axis x‖ ^ 2 = ‖x‖ ^ 2 - (inner ℝ axis x) ^ 2 := by
  rw [hingeRemainder, norm_sub_sq_real, inner_smul_right, norm_smul, unit, mul_one,
    Real.norm_eq_abs, sq_abs, real_inner_comm x axis]
  ring

theorem inner_eq_hinge_components {axis : E} (unit : ‖axis‖ = 1) (x y : E) :
    inner ℝ x y = inner ℝ axis x * inner ℝ axis y +
      inner ℝ (hingeRemainder axis x) (hingeRemainder axis y) := by
  simp only [hingeRemainder, inner_sub_left, inner_sub_right, real_inner_smul_left,
    inner_smul_right, real_inner_self_eq_norm_sq, unit, one_pow]
  rw [real_inner_comm x axis]
  ring

end Remainders

/-- In the plane, perpendicular vectors on opposite sides of a hinge point in opposite directions. -/
theorem opposite_perpendicular_inner (axis x y : Plane) (nonzero : axis ≠ 0)
    (x_perpendicular : inner ℝ axis x = 0) (y_perpendicular : inner ℝ axis y = 0)
    (opposite : inner ℝ x y ≤ 0) : inner ℝ x y = -‖x‖ * ‖y‖ := by
  by_cases x_zero : x = 0
  · simp [x_zero]
  let D := (Submodule.span ℝ ({axis} : Set Plane))ᗮ
  have dimension : Module.finrank ℝ D = 1 := by
    have sum := (Submodule.span ℝ ({axis} : Set Plane)).finrank_add_finrank_orthogonal
    rw [finrank_span_singleton nonzero] at sum
    have ambient : Module.finrank ℝ Plane = 2 := by simp [Plane]
    rw [ambient] at sum
    change 1 + Module.finrank ℝ D = 2 at sum
    omega
  have x_mem : x ∈ D := Submodule.mem_orthogonal_singleton_iff_inner_right.mpr x_perpendicular
  have y_mem : y ∈ D := Submodule.mem_orthogonal_singleton_iff_inner_right.mpr y_perpendicular
  obtain ⟨t, equal⟩ := exists_smul_eq_of_finrank_eq_one dimension
    (show (⟨x, x_mem⟩ : D) ≠ 0 from fun equal => x_zero (congrArg Subtype.val equal))
    (⟨y, y_mem⟩ : D)
  have y_eq : y = t • x := (congrArg Subtype.val equal).symm
  rw [y_eq, inner_smul_right, real_inner_self_eq_norm_sq] at opposite ⊢
  have norm_pos := norm_pos_iff.mpr x_zero
  have nonpositive : t ≤ 0 := by nlinarith [sq_pos_of_pos norm_pos]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonpos nonpositive]
  ring

end SixVertexUnfolding
