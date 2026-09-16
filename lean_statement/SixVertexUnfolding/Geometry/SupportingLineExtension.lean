import SixVertexUnfolding.Definitions

/-! Extend an increasing side direction to a supporting line while
remaining in the transverse plane. This supplies candidate outer corners
for the remaining angular-perimeter construction. -/

namespace SixVertexUnfolding

/-- An outward extension reaches the supporting line beyond the second point. -/
theorem extend_to_supporting_line (height side : Space →ₗ[ℝ] ℝ) (a b : Space)
    (level_a : height a = 1) (level_b : height b = 1)
    (increasing : side a < side b) (below : side b < 0) :
    ∃ p : Space, height p = 1 ∧ side p = 0 ∧ b ∈ openSegment ℝ a p := by
  let t := side a / (side a - side b)
  have denominator : side a - side b < 0 := sub_neg.mpr increasing
  have balance : t * (side a - side b) = side a := div_mul_cancel₀ _ denominator.ne
  have beyond : 1 < t := by nlinarith
  have t_positive : 0 < t := by linarith
  let p := AffineMap.lineMap a b t
  refine ⟨p, ?_, ?_, ?_⟩
  · change height (AffineMap.lineMap a b t) = 1
    simp only [AffineMap.lineMap_apply_module, map_add, map_smul, smul_eq_mul, level_a, level_b, mul_one]
    ring
  · change side (AffineMap.lineMap a b t) = 0
    simp only [AffineMap.lineMap_apply_module, map_add, map_smul, smul_eq_mul]
    nlinarith
  · have inv_positive : 0 < t⁻¹ := inv_pos.mpr t_positive
    have inv_small : t⁻¹ < 1 := (inv_lt_one₀ t_positive).mpr beyond
    refine ⟨1 - t⁻¹, t⁻¹, sub_pos.mpr inv_small, inv_positive, by ring, ?_⟩
    rw [← AffineMap.lineMap_apply_module]
    change AffineMap.lineMap a (AffineMap.lineMap a b t) t⁻¹ = b
    simp only [AffineMap.lineMap_lineMap_right, inv_mul_cancel₀ t_positive.ne', AffineMap.lineMap_apply_one]

end SixVertexUnfolding
