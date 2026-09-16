import SixVertexUnfolding.Geometry.HingeDeterminant

/-! Signed planar areas under rigid coordinate changes. -/

namespace SixVertexUnfolding

open Real

theorem plane_eq_axes (x : Plane) : x = x 0 • direction 0 + x 1 • direction (π / 2) := by
  ext i
  fin_cases i <;> simp [direction]

theorem det_linear_map (T : Plane →ₗ[ℝ] Plane) (x y : Plane) :
    det (T x) (T y) = det (T (direction 0)) (T (direction (π / 2))) * det x y := by
  have mapped (z : Plane) : T z = z 0 • T (direction 0) + z 1 • T (direction (π / 2)) := by
    calc
      T z = T (z 0 • direction 0 + z 1 • direction (π / 2)) := congrArg T (plane_eq_axes z)
      _ = _ := by rw [map_add, map_smul, map_smul]
  rw [mapped x, mapped y]
  simp only [det_add_left, det_add_right, det_smul_left, det_smul_right, det_self, mul_zero, add_zero, zero_add]
  have reverse : det (T (direction (π / 2))) (T (direction 0)) = -det (T (direction 0)) (T (direction (π / 2))) := det_swap _ _
  rw [reverse]
  change _ = _ * (x 0 * y 1 - x 1 * y 0)
  ring

theorem det_sq_add_inner_sq (x y : Plane) : det x y ^ 2 + inner ℝ x y ^ 2 = ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, Fin.sum_univ_two,
    plane_inner_coordinates]
  unfold det
  ring

theorem isometry_orientation_sq (T : Plane ≃ₗᵢ[ℝ] Plane) :
    det (T (direction 0)) (T (direction (π / 2))) ^ 2 = 1 := by
  have identity := det_sq_add_inner_sq (T (direction 0)) (T (direction (π / 2)))
  simp only [T.norm_map, T.inner_map_map, direction_norm, direction_inner, sub_zero, cos_pi_div_two,
    zero_pow (by decide : 2 ≠ 0), add_zero, one_pow, mul_one] at identity
  exact identity

/-- If a rigid coordinate change reverses one nondegenerate triangle, it reverses every signed area. -/
theorem isometry_det_reverses (T : Plane ≃ₗᵢ[ℝ] Plane) (a b : Plane)
    (before : det a b < 0) (after : 0 < det (T a) (T b)) :
    ∀ x y : Plane, det (T x) (T y) = -det x y := by
  let orientation := det (T (direction 0)) (T (direction (π / 2)))
  have squared : orientation ^ 2 = 1 := isometry_orientation_sq T
  change 0 < det (T.toLinearMap a) (T.toLinearMap b) at after
  rw [det_linear_map T.toLinearMap] at after
  change 0 < orientation * det a b at after
  have negative : orientation < 0 := by
    by_contra nonnegative
    have impossible := mul_nonpos_of_nonneg_of_nonpos (le_of_not_gt nonnegative) before.le
    linarith
  have factor : (orientation - 1) * (orientation + 1) = 0 := by nlinarith
  have orientation_eq : orientation = -1 := by
    rcases mul_eq_zero.mp factor with positive | negative_one <;> linarith
  intro x y
  change det (T.toLinearMap x) (T.toLinearMap y) = -det x y
  rw [det_linear_map T.toLinearMap]
  change orientation * det x y = -det x y
  rw [orientation_eq]
  ring

theorem det_ne_zero_of_noncollinear (a b c : Plane)
    (noncollinear : ¬ Collinear ℝ ({a, b, c} : Set Plane)) : det (b - a) (c - a) ≠ 0 := by
  have ab : a ≠ b := by
    intro same
    apply noncollinear
    simpa [same] using collinear_pair ℝ b c
  have unit := NormedSpace.norm_normalize (sub_ne_zero.mpr ab.symm : b - a ≠ 0)
  have positive : 0 < inner ℝ (hingeSideVector a b c) (hingeSideVector a b c) := by
    rw [real_inner_self_eq_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr (hingeSideVector_ne_zero a b c noncollinear))
  intro zero
  simp only [hingeSideVector] at positive
  rw [hingeRemainder_inner_eq_det _ _ _ unit] at positive
  simp only [NormedSpace.normalize, det_smul_left, zero, mul_zero] at positive
  linarith

end SixVertexUnfolding
