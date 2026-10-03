import SixVertexUnfolding.Geometry.FourTriangleSeparation

/-! A whole convex face occupies its corner cone. Thus the four-triangle
separation argument applies to polygons inside those same cones. -/

namespace SixVertexUnfolding.FourTriangleChain

open Real Set

/-- The full nonnegative cone between two consecutive rays. -/
def cornerCone (chain : FourTriangleChain) (i : Fin 4) : Set Plane :=
  {x | ∃ t u : ℝ, 0 ≤ t ∧ 0 ≤ u ∧ x - chain.center =
    t • (chain.ray i.castSucc - chain.center) + u • (chain.ray i.succ - chain.center)}

/-- Positive curvature separates the full corner cones, hence any whole polygons in them. -/
theorem cornerCone_nonoverlap (chain : FourTriangleChain)
    (one_turn : (∑ i : Fin 4, chain.corner i) < 2 * π)
    (i j : Fin 4) (different : i ≠ j) :
    Disjoint (interior (chain.cornerCone i)) (interior (chain.cornerCone j)) := by
  suffices ordered : ∀ i j : Fin 4, i < j →
      Disjoint (interior (chain.cornerCone i)) (interior (chain.cornerCone j)) by
    rcases lt_or_gt_of_ne different with before | after
    · exact ordered i j before
    · exact (ordered j i after).symm
  intro i j before
  obtain ⟨motion, at_center, at_ray⟩ := chain.exists_radial_motion
  have mono := chain.directionAngle_strictMono.monotone
  have left_order : chain.directionAngle i.castSucc ≤ chain.directionAngle i.succ := mono (by change i.val ≤ i.val + 1; omega)
  have between : chain.directionAngle i.succ ≤ chain.directionAngle j.castSucc := mono (by change i.val + 1 ≤ j.val; exact before)
  have right_order : chain.directionAngle j.castSucc ≤ chain.directionAngle j.succ := mono (by change j.val ≤ j.val + 1; omega)
  have full_turn : chain.directionAngle j.succ - chain.directionAngle i.castSucc ≤ 2 * π := by
    have lo := mono (show (0 : Fin 5) ≤ i.castSucc from Fin.zero_le _)
    have hi := mono (show j.succ ≤ (4 : Fin 5) from Fin.le_last _)
    have zero : chain.directionAngle 0 = 0 := rfl
    have last : chain.directionAngle 4 = ∑ k : Fin 4, chain.corner k := by rw [Fin.sum_univ_four]; rfl
    rw [zero] at lo
    rw [last] at hi
    linarith
  obtain ⟨θ, beta_le, le_gamma, delta_le, le_alpha⟩ := sector_separator_angle between
    (by rw [chain.directionAngle_step]; exact (chain.corner_lt_pi i).le)
    (by rw [chain.directionAngle_step]; exact (chain.corner_lt_pi j).le) full_turn
  have left_ray (x : ℝ) (hx : chain.directionAngle i.castSucc ≤ x)
      (hy : x ≤ chain.directionAngle i.succ) : det (direction θ) (direction x) ≤ 0 := by
    rw [direction_det]
    exact sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith)
  have right_ray (x : ℝ) (hx : chain.directionAngle j.castSucc ≤ x)
      (hy : x ≤ chain.directionAngle j.succ) : 0 ≤ det (direction θ) (direction x) := by
    rw [direction_det]
    exact sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have coordinates (k : Fin 4) (x : Plane) (hx : x ∈ chain.cornerCone k) :
      ∃ t u : ℝ, 0 ≤ t ∧ 0 ≤ u ∧
        motion x = t • chain.target k.castSucc + u • chain.target k.succ := by
    obtain ⟨t, u, ht, hu, equal⟩ := hx
    have mapped := congrArg motion.toAffineMap.linear equal
    have map_difference (v w : Plane) : motion.toAffineMap.linear (v - w) = motion v - motion w :=
      motion.toAffineMap.linearMap_vsub v w
    simp only [map_add, map_smul, map_difference, at_center, at_ray, sub_zero] at mapped
    exact ⟨t, u, ht, hu, mapped⟩
  have separated : Disjoint (interior (motion '' chain.cornerCone i))
      (interior (motion '' chain.cornerCone j)) := by
    apply disjoint_interiors_of_halfplanes (detHeight (direction θ)) (direction_height_surjective θ) 0
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨t, u, ht, hu, equal⟩ := coordinates i x hx
      change det (direction θ) (motion x) ≤ 0
      rw [equal, det_add_right, target, target, det_smul_right, det_smul_right,
        det_smul_right, det_smul_right]
      exact add_nonpos
        (mul_nonpos_of_nonneg_of_nonpos ht (mul_nonpos_of_nonneg_of_nonpos (chain.radius_pos _).le
          (left_ray _ le_rfl left_order)))
        (mul_nonpos_of_nonneg_of_nonpos hu (mul_nonpos_of_nonneg_of_nonpos (chain.radius_pos _).le
          (left_ray _ left_order le_rfl)))
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨t, u, ht, hu, equal⟩ := coordinates j x hx
      change 0 ≤ det (direction θ) (motion x)
      rw [equal, det_add_right, target, target, det_smul_right, det_smul_right,
        det_smul_right, det_smul_right]
      exact add_nonneg
        (mul_nonneg ht (mul_nonneg (chain.radius_pos _).le (right_ray _ le_rfl right_order)))
        (mul_nonneg hu (mul_nonneg (chain.radius_pos _).le (right_ray _ right_order le_rfl)))
  change Disjoint (interior (motion.toHomeomorph '' chain.cornerCone i))
    (interior (motion.toHomeomorph '' chain.cornerCone j)) at separated
  rw [← motion.toHomeomorph.image_interior, ← motion.toHomeomorph.image_interior] at separated
  exact (Set.disjoint_image_iff motion.injective).mp separated

end SixVertexUnfolding.FourTriangleChain
