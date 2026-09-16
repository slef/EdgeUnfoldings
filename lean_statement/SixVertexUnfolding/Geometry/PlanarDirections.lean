import SixVertexUnfolding.Definitions

/-! Ordinary Cartesian directions and determinants for the planar separation arguments. -/

namespace SixVertexUnfolding

open Real

/-- The unit direction making angle `θ` with the positive horizontal axis. -/
noncomputable def direction (θ : ℝ) : Plane := !₂[cos θ, sin θ]

/-- The signed area of the two planar vectors. -/
def det (x y : Plane) : ℝ := x 0 * y 1 - x 1 * y 0

@[simp] theorem direction_x (θ : ℝ) : direction θ 0 = cos θ := rfl
@[simp] theorem direction_y (θ : ℝ) : direction θ 1 = sin θ := rfl

theorem direction_norm (θ : ℝ) : ‖direction θ‖ = 1 := by
  have square : ‖direction θ‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    exact cos_sq_add_sin_sq θ
  nlinarith [norm_nonneg (direction θ)]

theorem direction_ne_zero (θ : ℝ) : direction θ ≠ 0 := by
  intro zero
  have unit := direction_norm θ
  simp [zero] at unit

theorem direction_inner (α β : ℝ) : inner ℝ (direction α) (direction β) = cos (β - α) := by
  simp only [PiLp.inner_apply, Fin.sum_univ_two, direction_x, direction_y, real_inner_eq_re_inner,
    RCLike.inner_apply, RCLike.conj_to_real, RCLike.re_to_real, cos_sub]

theorem direction_det (α β : ℝ) : det (direction α) (direction β) = sin (β - α) := by
  simp only [det, direction_x, direction_y, sin_sub]
  ring

theorem direction_angle (α β : ℝ) (lower : 0 ≤ β - α) (upper : β - α ≤ π) :
    InnerProductGeometry.angle (direction α) (direction β) = β - α := by
  rw [InnerProductGeometry.angle, direction_inner, direction_norm, direction_norm, mul_one, div_one]
  exact arccos_cos lower upper

/-- Cartesian polar coordinates realize the cosine law exactly. -/
theorem polar_distance_sq (r s α β : ℝ) :
    dist (r • direction α) (s • direction β) ^ 2 =
      r ^ 2 + s ^ 2 - 2 * r * s * cos (β - α) := by
  rw [dist_eq_norm, norm_sub_sq_real, norm_smul, norm_smul, direction_norm, direction_norm,
    mul_one, mul_one, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs,
    real_inner_smul_left, inner_smul_right, direction_inner]
  ring

theorem polar_radius (r θ : ℝ) (nonnegative : 0 ≤ r) : dist 0 (r • direction θ) = r := by
  rw [dist_zero_left, norm_smul, direction_norm, mul_one, Real.norm_eq_abs, abs_of_nonneg nonnegative]

theorem det_add_right (x y z : Plane) : det x (y + z) = det x y + det x z := by
  simp [det, PiLp.add_apply]
  ring

theorem det_sub_right (x y z : Plane) : det x (y - z) = det x y - det x z := by
  simp [det, PiLp.sub_apply]
  ring

theorem det_smul_right (x y : Plane) (r : ℝ) : det x (r • y) = r * det x y := by
  simp [det, PiLp.smul_apply]
  ring

/-- Signed area against a fixed direction is a continuous linear height. -/
noncomputable def detHeight (x : Plane) : Plane →L[ℝ] ℝ :=
  x 0 • EuclideanSpace.proj 1 - x 1 • EuclideanSpace.proj 0

@[simp] theorem detHeight_apply (x y : Plane) : detHeight x y = det x y := rfl

theorem direction_height_surjective (θ : ℝ) : Function.Surjective (detHeight (direction θ)) := by
  intro r
  refine ⟨r • direction (θ + π / 2), ?_⟩
  rw [detHeight_apply, det_smul_right, direction_det]
  simp

end SixVertexUnfolding
