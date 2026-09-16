import SixVertexUnfolding.Geometry.FourTriangleCone

/-! The complementary-cone argument at the other end of a four-triangle junction. -/

namespace SixVertexUnfolding.FourTriangleChain

open Real

/-- A reflex first two-triangle corner traps the last ray between the pole ray and the first cut ray. -/
theorem last_ray_in_complementary_cone (chain : FourTriangleChain)
    (one_turn : (∑ i : Fin 4, chain.corner i) < 2 * π)
    (reflex_head : π < chain.corner 0 + chain.corner 1) :
    chain.ray 4 - chain.center ∈ twoRayCone (chain.ray 2 - chain.center) (chain.ray 0 - chain.center) := by
  have last : chain.directionAngle 4 = ∑ i : Fin 4, chain.corner i := by
    rw [Fin.sum_univ_four]
    rfl
  have positive2 := chain.corner_pos 2
  have positive3 := chain.corner_pos 3
  have cone_direction : direction (chain.directionAngle 4) ∈
      twoRayCone (direction (chain.directionAngle 2)) (direction (2 * π)) := by
    apply direction_mem_twoRayCone
    · change 0 < 2 * π - (chain.corner 0 + chain.corner 1)
      rw [Fin.sum_univ_four] at one_turn
      linarith
    · change 2 * π - (chain.corner 0 + chain.corner 1) < π
      linarith
    · change chain.corner 0 + chain.corner 1 ≤
        chain.corner 0 + chain.corner 1 + chain.corner 2 + chain.corner 3
      linarith
    · rw [last]
      exact one_turn.le
  have full_turn : direction (2 * π) = direction 0 := by
    simpa only [zero_add] using direction_add_two_pi 0
  rw [full_turn] at cone_direction
  have scaled := mem_twoRayCone_scaled_generators _ _ _ (chain.radius 2) (chain.radius 0)
    (chain.radius_pos 2) (chain.radius_pos 0)
    (smul_mem_twoRayCone (chain.radius_pos 4).le cone_direction)
  obtain ⟨motion, at_center, at_ray⟩ := chain.exists_radial_motion
  apply (mem_twoRayCone_isometry motion.linearIsometryEquiv _ _ _).mp
  have difference (p q : Plane) : motion.linearIsometryEquiv (p - q) = motion p - motion q := motion.map_vsub p q
  rw [difference, difference, difference, at_center, at_ray, at_ray, at_ray, sub_zero, sub_zero, sub_zero]
  exact scaled

end SixVertexUnfolding.FourTriangleChain
