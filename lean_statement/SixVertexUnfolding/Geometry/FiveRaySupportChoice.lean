import SixVertexUnfolding.Geometry.FiveRayCoordinates

/-! Choose a side whose supporting line meets both sides of the opposite
corner beyond their neighbors. This supplies the enclosing triangle. -/

namespace SixVertexUnfolding.FiveRayFan

/-- The first side direction moves toward the supporting line two sides ahead. -/
def Advances (fan : FiveRayFan) (i : Fin 5) : Prop :=
  fan.side (i + 2) (fan.ray i) < fan.side (i + 2) (fan.ray (i + 1))

/-- A failed advancing direction forces the direction two places later to advance. -/
theorem advances_two_of_not_first (fan : FiveRayFan) (failure : ¬ fan.Advances 0) :
    fan.Advances 2 := by
  obtain ⟨a, b, c, ap, bn, _, total, combination⟩ := fan.fourth_coefficients
  have s23 : fan.side 2 (fan.ray 3) = 0 := fan.side_right 2
  have s40 : fan.side 4 (fan.ray 0) = 0 := fan.side_right 4
  have s20 := fan.side_strict 2 0 (by decide) (by decide)
  have s41 := fan.side_strict 4 1 (by decide) (by decide)
  have s42 := fan.side_strict 4 2 (by decide) (by decide)
  have first := congrArg (fan.side 2) combination
  have last := congrArg (fan.side 4) combination
  simp only [map_add, map_smul, smul_eq_mul, fan.side_left, s23, s40,
    mul_zero, zero_add, add_zero] at first last
  have backwards : fan.side 2 (fan.ray 1) ≤ fan.side 2 (fan.ray 0) := not_lt.mp failure
  have ab : 0 ≤ a + b := by
    by_contra h
    have positive := mul_pos_of_neg_of_neg (not_le.mp h) s20
    have comparison := mul_le_mul_of_nonpos_left backwards bn.le
    nlinarith
  change fan.side 4 (fan.ray 2) < fan.side 4 (fan.ray 3)
  have identity : fan.side 4 (fan.ray 3) - fan.side 4 (fan.ray 2) =
      b * fan.side 4 (fan.ray 1) - (a + b) * fan.side 4 (fan.ray 2) := by
    nlinarith [last]
  have positive := mul_pos_of_neg_of_neg bn s41
  have nonpositive := mul_nonpos_of_nonneg_of_nonpos ab s42.le
  linarith

/-- Advancing on the opposite side gives the second extension inequality. -/
theorem opposite_advance (fan : FiveRayFan) (advance : fan.Advances 2) :
    fan.side 2 (fan.ray 0) < fan.side 2 (fan.ray 4) := by
  obtain ⟨a, b, c, ap, _, _, total, fourth⟩ := fan.fourth_coefficients
  obtain ⟨u, v, w, _, wp, total', fifth⟩ := fan.fifth_coefficients
  have s23 : fan.side 2 (fan.ray 3) = 0 := fan.side_right 2
  have s40 : fan.side 4 (fan.ray 0) = 0 := fan.side_right 4
  have s21 := fan.side_strict 2 1 (by decide) (by decide)
  have s41 := fan.side_strict 4 1 (by decide) (by decide)
  have d2 := congrArg (fan.side 2) fourth
  have d4 := congrArg (fan.side 4) fourth
  have e2 := congrArg (fan.side 2) fifth
  have e4 := congrArg (fan.side 4) fifth
  simp only [map_add, map_smul, smul_eq_mul, fan.side_left, s23, s40,
    mul_zero, zero_add, add_zero] at d2 d4 e2 e4
  have balance :
      a * fan.side 4 (fan.ray 1) * (fan.side 2 (fan.ray 4) - fan.side 2 (fan.ray 0)) =
      w * fan.side 2 (fan.ray 1) * (fan.side 4 (fan.ray 3) - fan.side 4 (fan.ray 2)) := by
    linear_combination
      -a * fan.side 4 (fan.ray 1) * e2 + w * fan.side 2 (fan.ray 1) * d4 +
      a * fan.side 2 (fan.ray 0) * fan.side 4 (fan.ray 1) * total' -
      w * fan.side 2 (fan.ray 1) * fan.side 4 (fan.ray 2) * total +
      (a + b) * fan.side 2 (fan.ray 1) * e4 -
      (v + w) * fan.side 4 (fan.ray 1) * d2
  change fan.side 4 (fan.ray 2) < fan.side 4 (fan.ray 3) at advance
  by_contra h
  have nonnegative := mul_nonneg_of_nonpos_of_nonpos
    (mul_neg_of_pos_of_neg ap s41).le (sub_nonpos.mpr (not_lt.mp h))
  have negative := mul_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg wp s21) (sub_pos.mpr advance)
  linarith

/-- On an odd five-cycle, these implications force two consecutive advances. -/
private theorem five_cycle_pair (p : Fin 5 → Prop)
    (step : ∀ i, ¬ p i → p (i + 2)) : ∃ i, p i ∧ p (i + 2) := by
  by_contra none
  have exclude (i : Fin 5) : p i → ¬ p (i + 2) := by
    intro first second
    exact none ⟨i, first, second⟩
  have s0 := step 0
  have s1 := step 1
  have s2 := step 2
  have s3 := step 3
  have s4 := step 4
  have n0 := exclude 0
  have n1 := exclude 1
  have n2 := exclude 2
  have n3 := exclude 3
  have n4 := exclude 4
  norm_num at s0 s1 s2 s3 s4 n0 n1 n2 n3 n4
  tauto

/-- Some cyclic start admits both required extensions to the opposite supporting line. -/
theorem exists_enclosing_start (fan : FiveRayFan) :
    ∃ i : Fin 5, (fan.rotate i).side 2 ((fan.rotate i).ray 0) <
        (fan.rotate i).side 2 ((fan.rotate i).ray 1) ∧
      (fan.rotate i).side 2 ((fan.rotate i).ray 0) <
        (fan.rotate i).side 2 ((fan.rotate i).ray 4) := by
  have rotation (i j : Fin 5) : (fan.rotate i).Advances j ↔ fan.Advances (i + j) := by
    simp only [Advances, rotate, add_assoc]
  have step (i : Fin 5) (failure : ¬ fan.Advances i) : fan.Advances (i + 2) := by
    apply (rotation i 2).mp
    apply (fan.rotate i).advances_two_of_not_first
    simpa only [rotation, add_zero] using failure
  obtain ⟨i, first, second⟩ := five_cycle_pair fan.Advances step
  refine ⟨i, ?_, (fan.rotate i).opposite_advance ((rotation i 2).mpr second)⟩
  have := (rotation i 0).mpr (by simpa only [add_zero] using first)
  exact this

end SixVertexUnfolding.FiveRayFan
