import SixVertexUnfolding.Geometry.FourTriangleChain
import SixVertexUnfolding.Geometry.TriangleCones
import SixVertexUnfolding.Geometry.DirectionIdentities

/-! A reflex tail of a four-triangle junction traps the first ray inside the complementary cone. -/

namespace SixVertexUnfolding

open Real

theorem mem_twoRayCone_isometry (T : Plane ≃ₗᵢ[ℝ] Plane) (e f x : Plane) :
    T x ∈ twoRayCone (T e) (T f) ↔ x ∈ twoRayCone e f := by
  constructor
  · rintro ⟨a, b, ha, hb, equal⟩
    refine ⟨a, b, ha, hb, T.injective ?_⟩
    simpa only [map_add, map_smul] using equal
  · rintro ⟨a, b, ha, hb, equal⟩
    refine ⟨a, b, ha, hb, ?_⟩
    simpa only [map_add, map_smul] using congrArg T equal

theorem mem_twoRayCone_scaled_generators (e f x : Plane) (r s : ℝ) (r_pos : 0 < r) (s_pos : 0 < s)
    (member : x ∈ twoRayCone e f) : x ∈ twoRayCone (r • e) (s • f) := by
  obtain ⟨a, b, ha, hb, equal⟩ := member
  refine ⟨a / r, b / s, div_nonneg ha r_pos.le, div_nonneg hb s_pos.le, ?_⟩
  rw [smul_smul, smul_smul, div_mul_cancel₀ a r_pos.ne', div_mul_cancel₀ b s_pos.ne']
  exact equal

namespace FourTriangleChain

variable (chain : FourTriangleChain)

/-- A reflex last two-triangle corner leaves the first ray strictly between the pole ray and last cut ray. -/
theorem first_ray_in_complementary_cone (one_turn : (∑ i : Fin 4, chain.corner i) < 2 * π)
    (reflex_tail : π < chain.corner 2 + chain.corner 3) :
    chain.ray 0 - chain.center ∈ twoRayCone (chain.ray 2 - chain.center) (chain.ray 4 - chain.center) := by
  have last : chain.directionAngle 4 = ∑ i : Fin 4, chain.corner i := by
    rw [Fin.sum_univ_four]
    rfl
  have positive0 := chain.corner_pos 0
  have positive1 := chain.corner_pos 1
  have cone_direction : direction (2 * π) ∈
      twoRayCone (direction (chain.directionAngle 4)) (direction (chain.directionAngle 2 + 2 * π)) := by
    apply direction_mem_twoRayCone
    · rw [last]
      change 0 < chain.corner 0 + chain.corner 1 + 2 * π - _
      linarith
    · change chain.corner 0 + chain.corner 1 + 2 * π -
        (chain.corner 0 + chain.corner 1 + chain.corner 2 + chain.corner 3) < π
      linarith
    · rw [last]; exact one_turn.le
    · change 2 * π ≤ chain.corner 0 + chain.corner 1 + 2 * π
      linarith
  have full_turn : direction (2 * π) = direction 0 := by
    simpa only [zero_add] using direction_add_two_pi 0
  rw [full_turn, direction_add_two_pi, twoRayCone_swap] at cone_direction
  have scaled := mem_twoRayCone_scaled_generators _ _ _ (chain.radius 2) (chain.radius 4)
    (chain.radius_pos 2) (chain.radius_pos 4)
    (smul_mem_twoRayCone (chain.radius_pos 0).le cone_direction)
  obtain ⟨motion, at_center, at_ray⟩ := chain.exists_radial_motion
  apply (mem_twoRayCone_isometry motion.linearIsometryEquiv _ _ _).mp
  have difference (p q : Plane) : motion.linearIsometryEquiv (p - q) = motion p - motion q := motion.map_vsub p q
  rw [difference, difference, difference, at_center, at_ray, at_ray, at_ray, sub_zero, sub_zero, sub_zero]
  exact scaled

end FourTriangleChain
end SixVertexUnfolding
