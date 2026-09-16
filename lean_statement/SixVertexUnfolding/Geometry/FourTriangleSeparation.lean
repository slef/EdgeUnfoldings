import SixVertexUnfolding.Geometry.FourTriangleChain

/-! A four-triangle chain with total angle below one turn has no overlapping triangle interiors. -/

namespace SixVertexUnfolding.FourTriangleChain

open Real

variable (chain : FourTriangleChain)

/-- Positive curvature at the common vertex separates every pair in its developed four-triangle chain. -/
theorem nonoverlap (one_turn : (∑ i : Fin 4, chain.corner i) < 2 * π)
    (i j : Fin 4) (different : i ≠ j) :
    Disjoint (interior (chain.triangle i)) (interior (chain.triangle j)) := by
  suffices ordered : ∀ i j : Fin 4, i < j →
      Disjoint (interior (chain.triangle i)) (interior (chain.triangle j)) by
    rcases lt_or_gt_of_ne different with before | after
    · exact ordered i j before
    · exact (ordered j i after).symm
  intro i j before
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
  have left_order : chain.directionAngle i.castSucc ≤ chain.directionAngle i.succ := mono (by change i.val ≤ i.val + 1; omega)
  have between : chain.directionAngle i.succ ≤ chain.directionAngle j.castSucc := by
    apply mono
    change i.val + 1 ≤ j.val
    exact before
  have right_order : chain.directionAngle j.castSucc ≤ chain.directionAngle j.succ := mono (by change j.val ≤ j.val + 1; omega)
  have full_turn : chain.directionAngle j.succ - chain.directionAngle i.castSucc ≤ 2 * π := by
    have lo := mono (show (0 : Fin 5) ≤ i.castSucc from Fin.zero_le _)
    have hi := mono (show j.succ ≤ (4 : Fin 5) from Fin.le_last _)
    have zero : chain.directionAngle 0 = 0 := rfl
    have last : chain.directionAngle 4 = ∑ k : Fin 4, chain.corner k := by
      rw [Fin.sum_univ_four]
      rfl
    rw [zero] at lo
    rw [last] at hi
    linarith
  have separated := radial_triangles_disjoint (chain.radius_pos i.castSucc).le (chain.radius_pos i.succ).le
    (chain.radius_pos j.castSucc).le (chain.radius_pos j.succ).le left_order between right_order
    (by rw [chain.directionAngle_step]; exact (chain.corner_lt_pi i).le)
    (by rw [chain.directionAngle_step]; exact (chain.corner_lt_pi j).le) full_turn
  rw [← placed i, ← placed j] at separated
  change Disjoint (interior (motion.toHomeomorph '' chain.triangle i))
    (interior (motion.toHomeomorph '' chain.triangle j)) at separated
  rw [← motion.toHomeomorph.image_interior, ← motion.toHomeomorph.image_interior] at separated
  exact (Set.disjoint_image_iff motion.injective).mp separated

end SixVertexUnfolding.FourTriangleChain
