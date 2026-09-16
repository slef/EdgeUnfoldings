import SixVertexUnfolding.Geometry.PolarRotations
import SixVertexUnfolding.Geometry.PolarArcs

/-! A wedge symmetric about a ray has a coordinate-free description by
ordinary angle from that ray. Reflections therefore cause no ambiguity. -/

namespace SixVertexUnfolding

open Set Real EuclideanGeometry

/-- The ordinary angle never exceeds an unwrapped polar difference. -/
theorem polar_angle_le_abs (r α β : ℝ) (positive : 0 < r) :
    angle (direction α) 0 (r • direction β) ≤ |β - α| := by
  have cosine_bound (x : ℝ) : arccos (cos x) ≤ |x| := by
    by_cases short : |x| ≤ π
    · rw [← cos_abs, arccos_cos (abs_nonneg x) short]
    · exact (arccos_le_pi _).trans (le_of_not_ge short)
  unfold angle
  simp only [vsub_eq_sub, sub_zero]
  rw [InnerProductGeometry.angle_smul_right_of_pos _ _ positive,
    InnerProductGeometry.angle, direction_inner, direction_norm, direction_norm, mul_one, div_one]
  exact cosine_bound _

/-- Every nonzero point lies at plus or minus its ordinary angle from a chosen ray. -/
theorem polar_point_signed_angle (α : ℝ) (x : Plane) (nonzero : x ≠ 0) :
    x = dist 0 x • direction (α + angle (direction α) 0 x) ∨
      x = dist 0 x • direction (α - angle (direction α) 0 x) := by
  let φ := angle (direction α) 0 x
  have positive : 0 < dist 0 x := dist_pos.mpr nonzero.symm
  have sine : 0 ≤ sin φ := sin_nonneg_of_nonneg_of_le_pi (angle_nonneg _ _ _) (angle_le_pi _ _ _)
  by_cases above : 0 ≤ det (direction α) x
  · left
    apply polar_point_eq_of_cos_and_side 1 (dist 0 x) α (α + φ) (by norm_num) positive x rfl
    · simp only [one_smul, add_sub_cancel_left, φ]
    · rw [add_sub_cancel_left]
      exact mul_nonneg above sine
  · right
    apply polar_point_eq_of_cos_and_side 1 (dist 0 x) α (α - φ) (by norm_num) positive x rfl
    · simp only [one_smul, sub_sub_cancel_left, cos_neg, φ]
    · rw [show α - φ - α = -φ by ring, sin_neg]
      exact mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge above) (neg_nonpos.mpr sine)

namespace Wedge

/-- Membership in a centered wedge depends only on radius and ordinary angle.
This includes empty, complete, and bounded circular sections. -/
theorem centered_polarRegion_iff (d ω axis half : ℝ) (x : Plane) :
    x ∈ polarRegion d ω (axis - half) (axis + half) ↔
      x = 0 ∨ angle (direction axis) 0 x ≤ half - offset d ω (dist 0 x) := by
  constructor
  · rintro (zero | ⟨ρ, θ, positive, position, lower, upper⟩)
    · exact Or.inl zero
    · right
      have radius : dist 0 x = ρ := by rw [position, polar_radius _ _ positive.le]
      rw [radius, position]
      apply (polar_angle_le_abs ρ axis θ positive).trans
      rw [abs_le]
      constructor <;> linarith
  · rintro (zero | bound)
    · exact Or.inl zero
    · by_cases zero : x = 0
      · exact Or.inl zero
      have positive : 0 < dist 0 x := dist_pos.mpr (Ne.symm zero)
      have nonnegative := angle_nonneg (direction axis) 0 x
      rcases polar_point_signed_angle axis x zero with plus | minus
      · exact Or.inr ⟨dist 0 x, axis + angle (direction axis) 0 x, positive,
          plus, by linarith, by linarith⟩
      · exact Or.inr ⟨dist 0 x, axis - angle (direction axis) 0 x, positive,
          minus, by linarith, by linarith⟩

/-- Any linear isometry preserving the chosen axis preserves the centered wedge,
including an isometry that reverses orientation. -/
theorem centered_polarRegion_image (turn : Plane ≃ₗᵢ[ℝ] Plane) (axis other : ℝ)
    (axis_maps : turn (direction axis) = direction other) (d ω half : ℝ) :
    turn '' polarRegion d ω (axis - half) (axis + half) =
      polarRegion d ω (other - half) (other + half) := by
  have membership (x : Plane) :
      turn x ∈ polarRegion d ω (other - half) (other + half) ↔
        x ∈ polarRegion d ω (axis - half) (axis + half) := by
    rw [centered_polarRegion_iff, centered_polarRegion_iff]
    have angle_maps := turn.toAffineIsometryEquiv.toAffineIsometry.angle_map (direction axis) 0 x
    change angle (turn (direction axis)) (turn 0) (turn x) = angle (direction axis) 0 x at angle_maps
    rw [axis_maps, map_zero] at angle_maps
    have radius : dist 0 (turn x) = dist 0 x := by
      rw [dist_zero_left, turn.norm_map, dist_zero_left]
    have zero_iff : turn x = 0 ↔ x = 0 := by
      constructor
      · intro zero
        exact turn.injective (zero.trans (map_zero turn).symm)
      · intro zero
        rw [zero, map_zero]
    rw [radius, angle_maps, zero_iff]
  ext y
  constructor
  · rintro ⟨x, member, rfl⟩
    exact (membership x).mpr member
  · intro member
    exact ⟨turn.symm y, (membership (turn.symm y)).mp (by simpa using member), turn.apply_symm_apply y⟩

end Wedge
end SixVertexUnfolding
