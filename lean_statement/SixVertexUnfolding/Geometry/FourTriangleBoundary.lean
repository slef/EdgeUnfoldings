import SixVertexUnfolding.Geometry.FourTriangleChain
import SixVertexUnfolding.Geometry.StrictPlanarSectors

/-! Nonneighboring triangles of a positively curved junction meet only at the shared vertex. -/

namespace SixVertexUnfolding.FourTriangleChain

open Real

variable (chain : FourTriangleChain)

/-- An intervening positive corner and the positive curvature gap exclude every other closed contact. -/
theorem meet_only_at_center (one_turn : (∑ k : Fin 4, chain.corner k) < 2 * π)
    (i j : Fin 4) (intervening : i.val + 1 < j.val)
    (x : Plane) (left : x ∈ chain.triangle i) (right : x ∈ chain.triangle j) : x = chain.center := by
  obtain ⟨motion, at_center, at_ray⟩ := chain.exists_radial_motion
  have placed (k : Fin 4) : motion '' chain.triangle k =
      radialTriangle (chain.radius k.castSucc) (chain.radius k.succ)
        (chain.directionAngle k.castSucc) (chain.directionAngle k.succ) := by
    change motion.toAffineMap '' convexHull ℝ _ = _
    rw [motion.toAffineMap.image_convexHull]
    simp only [Set.image_insert_eq, Set.image_singleton]
    change convexHull ℝ ({motion chain.center, motion (chain.ray k.castSucc), motion (chain.ray k.succ)} : Set Plane) = _
    rw [at_center, at_ray, at_ray]
    rfl
  have mono := chain.directionAngle_strictMono.monotone
  have full_turn : chain.directionAngle j.succ - chain.directionAngle i.castSucc < 2 * π := by
    have lo := mono (show (0 : Fin 5) ≤ i.castSucc from Fin.zero_le _)
    have hi := mono (show j.succ ≤ (4 : Fin 5) from Fin.le_last _)
    have zero : chain.directionAngle 0 = 0 := rfl
    have last : chain.directionAngle 4 = ∑ k : Fin 4, chain.corner k := by rw [Fin.sum_univ_four]; rfl
    rw [zero] at lo
    rw [last] at hi
    linarith
  have image_zero : motion x = 0 := by
    apply radial_triangles_meet_only_at_zero (chain.radius_pos i.castSucc) (chain.radius_pos i.succ)
      (chain.radius_pos j.castSucc) (chain.radius_pos j.succ)
      (mono (by change i.val ≤ i.val + 1; omega))
      (chain.directionAngle_strictMono (show i.succ < j.castSucc from intervening))
      (mono (by change j.val ≤ j.val + 1; omega))
      (by rw [chain.directionAngle_step]; exact chain.corner_lt_pi i)
      (by rw [chain.directionAngle_step]; exact chain.corner_lt_pi j) full_turn
    · rw [← placed i]
      exact Set.mem_image_of_mem motion left
    · rw [← placed j]
      exact Set.mem_image_of_mem motion right
  exact motion.injective (image_zero.trans at_center.symm)

end SixVertexUnfolding.FourTriangleChain
