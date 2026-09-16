import SixVertexUnfolding.Geometry.FourRayDiagonals

/-! A supported transverse fan has strictly positive angular deficit, including flat corners. -/

namespace SixVertexUnfolding.FourRayFan

open InnerProductGeometry

variable (fan : FourRayFan)

/-- The nonnegative diagonal relation has a nonzero difference of two adjacent weighted rays. -/
theorem diagonal_difference_ne_zero (α β γ δ : ℝ)
    (left_total : α + γ = 1) (right_total : β + δ = 1)
    (balance : α • fan.ray 0 + γ • fan.ray 2 = β • fan.ray 1 + δ • fan.ray 3) :
    α • fan.ray 0 - β • fan.ray 1 ≠ 0 := by
  intro zero
  have adjacent : α • fan.ray 0 = β • fan.ray 1 := sub_eq_zero.mp zero
  have same_coeff := congrArg fan.height adjacent
  simp only [map_smul, smul_eq_mul, fan.level, mul_one] at same_coeff
  by_cases α_zero : α = 0
  · have β_zero : β = 0 := same_coeff ▸ α_zero
    have γ_one : γ = 1 := by linarith
    have δ_one : δ = 1 := by linarith
    have same : fan.ray 2 = fan.ray 3 := by
      simpa only [α_zero, β_zero, γ_one, δ_one, zero_smul, one_smul, zero_add] using balance
    exact (by decide : (2 : Fin 4) ≠ 3) (fan.distinct same)
  · rw [← same_coeff] at adjacent
    have same := congrArg (fun x : Space => α⁻¹ • x) adjacent
    simp only [smul_smul, inv_mul_cancel₀ α_zero, one_smul] at same
    exact (by decide : (0 : Fin 4) ≠ 1) (fan.distinct same)

/-- The four successive angular sectors sum to strictly less than a full turn. -/
theorem perimeter_lt_two_pi :
    angle (fan.ray 0) (fan.ray 1) + angle (fan.ray 1) (fan.ray 2) +
      angle (fan.ray 2) (fan.ray 3) + angle (fan.ray 3) (fan.ray 0) < 2 * Real.pi := by
  obtain ⟨x, first, second⟩ := fan.diagonals_meet
  obtain ⟨α, γ, hα, hγ, left_total, left⟩ := first
  obtain ⟨β, δ, hβ, hδ, right_total, right⟩ := second
  have balance := left.trans right.symm
  exact spherical_quadrilateral_perimeter_lt fan.height (fan.ray 0) (fan.ray 1) (fan.ray 2) (fan.ray 3)
    (by rw [fan.level]; norm_num) (by rw [fan.level]; norm_num)
    (by rw [fan.level]; norm_num) (by rw [fan.level]; norm_num)
    α β γ δ hα hβ hγ hδ balance (fan.diagonal_difference_ne_zero α β γ δ left_total right_total balance)

/-- Sum notation for the same strict angular perimeter bound. -/
theorem sum_angles_lt_two_pi :
    ∑ i : Fin 4, angle (fan.ray i) (fan.ray (i + 1)) < 2 * Real.pi := by
  simpa only [Fin.sum_univ_four] using fan.perimeter_lt_two_pi

end SixVertexUnfolding.FourRayFan
