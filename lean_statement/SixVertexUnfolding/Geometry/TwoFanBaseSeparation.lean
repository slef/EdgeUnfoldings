import SixVertexUnfolding.Geometry.TwoFanFrame
import SixVertexUnfolding.Geometry.ThreeCornerCones
import SixVertexUnfolding.Geometry.FourCornerCones
import SixVertexUnfolding.Geometry.BaseConeSeparation

/-! Case B for the two actual outward fans of a triangular cap. -/

namespace SixVertexUnfolding

open Real

/-- If both angular sums reach π, the two outer whole-face cones cannot meet. -/
theorem two_fan_base_cones_disjoint (left : ThreeTriangleChain) (right : FourTriangleChain)
    (right_center : right.center = left.ray 1)
    (common_apex : right.ray 0 = left.ray 0) (left_center : right.ray 1 = left.center)
    (left_turn : (∑ i, left.corner i) < 2 * π)
    (right_turn : (∑ i, right.corner i) < 2 * π)
    (outer_sum : π ≤ (2 * π - (left.corner 1 + left.corner 2)) +
      (2 * π - (right.corner 1 + right.corner 2 + right.corner 3)))
    (fan_sum : π ≤ left.corner 1 + (right.corner 1 + right.corner 2)) :
    Disjoint (left.cornerCone 2) (right.cornerCone 3) := by
  let α := 2 * π - (left.corner 1 + left.corner 2)
  let β := 2 * π - (right.corner 1 + right.corner 2 + right.corner 3)
  let σ := left.corner 1
  let τ := right.corner 1 + right.corner 2
  have α_pos : 0 < α := by
    rw [Fin.sum_univ_three] at left_turn
    dsimp [α]; linarith [left.corner_pos 0]
  have β_pos : 0 < β := by
    rw [Fin.sum_univ_four] at right_turn
    dsimp [β]; linarith [right.corner_pos 0]
  have separated := base_cones_disjoint (left.radius 1) α β σ τ (left.radius_pos 1)
    α_pos β_pos (left.corner_pos 1) (add_pos (right.corner_pos 1) (right.corner_pos 2))
    (by dsimp [α, σ]; linarith [left.corner_pos 2])
    (by dsimp [β, τ]; linarith [right.corner_pos 3])
    (by dsimp [α, σ]; linarith [left.corner_lt_pi 2])
    (by dsimp [β, τ]; linarith [right.corner_lt_pi 3]) outer_sum fan_sum
  obtain ⟨motion, at_left, at_right, left_rays, right_rays⟩ :=
    exists_two_fan_cap_frame left right right_center common_apex left_center
  have difference (v w : Plane) : motion.toAffineMap.linear (v - w) = motion v - motion w :=
    motion.toAffineMap.linearMap_vsub v w
  have left_first : direction (left.capDirections 2) = direction (2 * π - σ) := by
    rw [direction_two_pi_sub]; rfl
  have left_last : direction (left.capDirections 3) = direction α := by
    dsimp [ThreeTriangleChain.capDirections, α]
    rw [direction_two_pi_sub]
    congr 1
    ring
  have right_first : direction (right.capDirections 3) = -direction τ := by
    change direction (π + right.corner 1 + right.corner 2) = _
    rw [show π + right.corner 1 + right.corner 2 = τ + π by dsimp [τ]; ring,
      direction_add_pi]
  have right_last : direction (right.capDirections 4) = -direction (2 * π - β) := by
    change direction (π + right.corner 1 + right.corner 2 + right.corner 3) = _
    rw [show π + right.corner 1 + right.corner 2 + right.corner 3 = (2 * π - β) + π by
      dsimp [β]; ring, direction_add_pi]
  have left_subset : motion '' left.cornerCone 2 ⊆
      translatedCone 0 (direction α) (direction (2 * π - σ)) := by
    rintro _ ⟨x, ⟨t, u, ht, hu, coords⟩, rfl⟩
    have mapped := congrArg motion.toAffineMap.linear coords
    simp only [map_add, map_smul, difference] at mapped
    change motion x - motion left.center =
      t • (motion (left.ray 2) - motion left.center) +
      u • (motion (left.ray 3) - motion left.center) at mapped
    rw [left_rays 2, left_rays 3, left_first, left_last, at_left] at mapped
    refine ⟨u * left.radius 3, t * left.radius 2,
      mul_nonneg hu (left.radius_pos 3).le, mul_nonneg ht (left.radius_pos 2).le, ?_⟩
    rw [mapped, mul_smul, mul_smul, add_comm]
  have right_subset : motion '' right.cornerCone 3 ⊆
      translatedCone (left.radius 1 • direction 0) (-direction τ) (-direction (2 * π - β)) := by
    rintro _ ⟨x, ⟨t, u, ht, hu, coords⟩, rfl⟩
    have mapped := congrArg motion.toAffineMap.linear coords
    simp only [map_add, map_smul, difference] at mapped
    change motion x - motion right.center =
      t • (motion (right.ray 3) - motion right.center) +
      u • (motion (right.ray 4) - motion right.center) at mapped
    rw [right_rays 3, right_rays 4, right_first, right_last, at_right] at mapped
    refine ⟨t * right.radius 3, u * right.radius 4,
      mul_nonneg ht (right.radius_pos 3).le, mul_nonneg hu (right.radius_pos 4).le, ?_⟩
    simpa only [mul_smul] using mapped
  exact (Set.disjoint_image_iff motion.injective).mp (separated.mono left_subset right_subset)

end SixVertexUnfolding
