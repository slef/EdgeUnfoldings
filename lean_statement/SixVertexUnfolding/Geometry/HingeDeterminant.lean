import SixVertexUnfolding.Geometry.PlanarDirections
import SixVertexUnfolding.Geometry.HingeSideOrder

/-! The geometric hinge-side condition is exactly the usual signed-area condition. -/

namespace SixVertexUnfolding

theorem plane_inner_coordinates (x y : Plane) : inner ℝ x y = x 0 * y 0 + x 1 * y 1 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_two, real_inner_eq_re_inner,
    RCLike.inner_apply, RCLike.conj_to_real, RCLike.re_to_real]
  ring

theorem det_smul_left (x y : Plane) (r : ℝ) : det (r • x) y = r * det x y := by
  simp [det, PiLp.smul_apply]
  ring

theorem det_add_left (x y z : Plane) : det (x + y) z = det x z + det y z := by
  simp [det, PiLp.add_apply]
  ring

theorem det_neg_left (x y : Plane) : det (-x) y = -det x y := by
  simp [det, PiLp.neg_apply]
  ring

theorem det_neg_right (x y : Plane) : det x (-y) = -det x y := by
  simp [det, PiLp.neg_apply]
  ring

theorem det_self (x : Plane) : det x x = 0 := by unfold det; ring

theorem det_swap (x y : Plane) : det x y = -det y x := by unfold det; ring

/-- A unit axis decomposes the dot product into its longitudinal and signed transverse components. -/
theorem inner_eq_axis_det (axis x y : Plane) (unit : ‖axis‖ = 1) :
    inner ℝ x y = inner ℝ axis x * inner ℝ axis y + det axis x * det axis y := by
  have square : axis 0 ^ 2 + axis 1 ^ 2 = 1 := by
    have norm_square := EuclideanSpace.real_norm_sq_eq axis
    rw [unit, one_pow, Fin.sum_univ_two] at norm_square
    exact norm_square.symm
  simp only [plane_inner_coordinates, det]
  linear_combination -(x 0 * y 0 + x 1 * y 1) * square

theorem hingeRemainder_inner_eq_det (axis x y : Plane) (unit : ‖axis‖ = 1) :
    inner ℝ (hingeRemainder axis x) (hingeRemainder axis y) = det axis x * det axis y := by
  have components := inner_eq_hinge_components unit x y
  have area := inner_eq_axis_det axis x y unit
  linarith

/-- Replacing perpendicular projections by signed determinants preserves the exact opposite-side predicate. -/
theorem oppositeHingeSides_iff_det (a b x y : Plane) (different : a ≠ b) :
    OppositeHingeSides a b x y ↔ det (b - a) (x - a) * det (b - a) (y - a) ≤ 0 := by
  have axis_ne : b - a ≠ 0 := sub_ne_zero.mpr different.symm
  have unit := NormedSpace.norm_normalize axis_ne
  rw [OppositeHingeSides, hingeSideVector, hingeSideVector, hingeRemainder_inner_eq_det _ _ _ unit]
  simp only [NormedSpace.normalize, det_smul_left]
  have factor : 0 < (‖b - a‖⁻¹) ^ 2 := sq_pos_of_pos (inv_pos.mpr (norm_pos_iff.mpr axis_ne))
  have expression : ‖b - a‖⁻¹ * det (b - a) (x - a) * (‖b - a‖⁻¹ * det (b - a) (y - a)) =
      (‖b - a‖⁻¹) ^ 2 * (det (b - a) (x - a) * det (b - a) (y - a)) := by ring
  rw [expression]
  constructor
  · intro nonpositive
    nlinarith
  · intro nonpositive
    exact mul_nonpos_of_nonneg_of_nonpos factor.le nonpositive

end SixVertexUnfolding
