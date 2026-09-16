import SixVertexUnfolding.Geometry.SphericalAngles

/-! The five-sided transverse figure needed at a degree-five vertex.
The strict total-angle bound is separate from these geometric data. -/

namespace SixVertexUnfolding

/-- Five cyclic rays and their actual supporting sides in a transverse plane. -/
structure FiveRayFan where
  ray : Fin 5 → Space
  distinct : Function.Injective ray
  height : Space →ₗ[ℝ] ℝ
  level : ∀ i, height (ray i) = 1
  spans : Submodule.span ℝ (Set.range ray) = ⊤
  side : Fin 5 → Space →ₗ[ℝ] ℝ
  side_nonzero : ∀ i, side i ≠ 0
  side_left : ∀ i, side i (ray i) = 0
  side_right : ∀ i, side i (ray (i + 1)) = 0
  side_bound : ∀ i j, side i (ray j) ≤ 0
  side_strict : ∀ i j, j ≠ i → j ≠ i + 1 → side i (ray j) < 0

namespace FiveRayFan

/-- Distinct normalized rays have a strictly positive angle. -/
theorem angle_pos (fan : FiveRayFan) {i j : Fin 5} (different : i ≠ j) :
    0 < InnerProductGeometry.angle (fan.ray i) (fan.ray j) := by
  by_contra not_positive
  have zero := le_antisymm (not_lt.mp not_positive) (InnerProductGeometry.angle_nonneg _ _)
  obtain ⟨_, r, _, same_ray⟩ := InnerProductGeometry.angle_eq_zero_iff.mp zero
  have same_height := congrArg fan.height same_ray
  simp only [map_smul, smul_eq_mul, fan.level, mul_one] at same_height
  have same : fan.ray j = fan.ray i := by simpa only [← same_height, one_smul] using same_ray
  exact different (fan.distinct same).symm

/-- Every sector is strictly smaller than a straight angle. -/
theorem sector_angle_lt_pi (fan : FiveRayFan) (i : Fin 5) :
    InnerProductGeometry.angle (fan.ray i) (fan.ray (i + 1)) < Real.pi :=
  angle_lt_pi_of_positive_height fan.height _ _ (by rw [fan.level]; norm_num)
    (by rw [fan.level]; norm_num)

end FiveRayFan
end SixVertexUnfolding
