import SixVertexUnfolding.Geometry.FiveRayFan

/-! Coordinates in the transverse plane of a supported pentagon.
Three consecutive rays form a basis; their coefficients describe the
remaining corners without choosing an orthonormal coordinate system. -/

namespace SixVertexUnfolding.FiveRayFan

open Set

/-- Start the same supported pentagon at any chosen corner. -/
def rotate (fan : FiveRayFan) (i : Fin 5) : FiveRayFan where
  ray := fun j => fan.ray (i + j)
  distinct := fun _ _ same => add_left_cancel (fan.distinct same)
  height := fan.height
  level := fun j => fan.level (i + j)
  spans := by
    have points : range (fun j => fan.ray (i + j)) = range fan.ray := by
      ext x
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨i + j, rfl⟩
      · rintro ⟨j, rfl⟩
        exact ⟨j - i, by simp⟩
    rw [points]
    exact fan.spans
  side := fun j => fan.side (i + j)
  side_nonzero := fun j => fan.side_nonzero (i + j)
  side_left := fun j => fan.side_left (i + j)
  side_right := fun j => by simpa only [add_assoc] using fan.side_right (i + j)
  side_bound := fun j k => fan.side_bound (i + j) (i + k)
  side_strict := by
    intro j k first second
    exact fan.side_strict (i + j) (i + k)
      (fun same => first (add_left_cancel same))
      (fun same => second (add_left_cancel (same.trans (add_assoc i j 1))))

/-- Three successive normalized rays are linearly independent. -/
theorem first_three_independent (fan : FiveRayFan) :
    LinearIndependent ℝ ![fan.ray 0, fan.ray 1, fan.ray 2] := by
  apply Fintype.linearIndependent_iff.mpr
  intro w combination
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two] at combination
  change w 0 • fan.ray 0 + w 1 • fan.ray 1 + w 2 • fan.ray 2 = 0 at combination
  have first := congrArg (fan.side 0) combination
  have second := congrArg (fan.side 1) combination
  have total := congrArg fan.height combination
  have s01 : fan.side 0 (fan.ray 1) = 0 := fan.side_right 0
  have s12 : fan.side 1 (fan.ray 2) = 0 := fan.side_right 1
  have s02 := fan.side_strict 0 2 (by decide) (by decide)
  have s10 := fan.side_strict 1 0 (by decide) (by decide)
  simp only [map_add, map_smul, smul_eq_mul, map_zero, fan.side_left,
    s01, s12, mul_zero, zero_add, add_zero] at first second
  simp only [map_add, map_smul, smul_eq_mul, map_zero, fan.level, mul_one] at total
  have w2 : w 2 = 0 := (mul_eq_zero.mp first).resolve_right s02.ne
  have w0 : w 0 = 0 := (mul_eq_zero.mp second).resolve_right s10.ne
  have w1 : w 1 = 0 := by linarith
  intro i
  fin_cases i <;> assumption

/-- Every vector has coefficients in the three consecutive ray directions. -/
theorem exists_coefficients (fan : FiveRayFan) (x : Space) :
    ∃ a b c : ℝ, a • fan.ray 0 + b • fan.ray 1 + c • fan.ray 2 = x := by
  have full := fan.first_three_independent.span_eq_top_of_card_eq_finrank (by simp [Space])
  have member : x ∈ Submodule.span ℝ (range ![fan.ray 0, fan.ray 1, fan.ray 2]) := by
    rw [full]
    trivial
  simp only [Matrix.range_cons, Matrix.range_empty, union_empty, singleton_union] at member
  simpa only [add_assoc] using Submodule.mem_span_triple.mp member

/-- On the transverse plane, the coefficients sum to one. -/
theorem coefficient_sum (fan : FiveRayFan) {x : Space} {a b c : ℝ}
    (level : fan.height x = 1)
    (combination : a • fan.ray 0 + b • fan.ray 1 + c • fan.ray 2 = x) :
    a + b + c = 1 := by
  have measured := congrArg fan.height combination
  simpa only [map_add, map_smul, smul_eq_mul, fan.level, mul_one, level] using measured

/-- The fourth corner lies beyond the side through the first and third corners. -/
theorem fourth_coefficients (fan : FiveRayFan) :
    ∃ a b c : ℝ, 0 < a ∧ b < 0 ∧ 0 < c ∧ a + b + c = 1 ∧
      a • fan.ray 0 + b • fan.ray 1 + c • fan.ray 2 = fan.ray 3 := by
  obtain ⟨a, b, c, combination⟩ := fan.exists_coefficients (fan.ray 3)
  have s01 : fan.side 0 (fan.ray 1) = 0 := fan.side_right 0
  have s12 : fan.side 1 (fan.ray 2) = 0 := fan.side_right 1
  have s23 : fan.side 2 (fan.ray 3) = 0 := fan.side_right 2
  have s02 := fan.side_strict 0 2 (by decide) (by decide)
  have s03 := fan.side_strict 0 3 (by decide) (by decide)
  have s10 := fan.side_strict 1 0 (by decide) (by decide)
  have s13 := fan.side_strict 1 3 (by decide) (by decide)
  have s20 := fan.side_strict 2 0 (by decide) (by decide)
  have s21 := fan.side_strict 2 1 (by decide) (by decide)
  have first := congrArg (fan.side 0) combination
  have second := congrArg (fan.side 1) combination
  have third := congrArg (fan.side 2) combination
  simp only [map_add, map_smul, smul_eq_mul, fan.side_left,
    s01, s12, s23, mul_zero, zero_add, add_zero] at first second third
  have ap : 0 < a := by
    by_contra h
    have := mul_nonneg_of_nonpos_of_nonpos (not_lt.mp h) s10.le
    nlinarith
  have cp : 0 < c := by
    by_contra h
    have := mul_nonneg_of_nonpos_of_nonpos (not_lt.mp h) s02.le
    nlinarith
  have bn : b < 0 := by
    by_contra h
    have := mul_nonpos_of_nonneg_of_nonpos (not_lt.mp h) s21.le
    nlinarith [mul_neg_of_pos_of_neg ap s20]
  exact ⟨a, b, c, ap, bn, cp, fan.coefficient_sum (fan.level 3) combination, combination⟩

/-- At the fifth corner the second coefficient is negative and the third is positive. -/
theorem fifth_coefficients (fan : FiveRayFan) :
    ∃ a b c : ℝ, b < 0 ∧ 0 < c ∧ a + b + c = 1 ∧
      a • fan.ray 0 + b • fan.ray 1 + c • fan.ray 2 = fan.ray 4 := by
  obtain ⟨a, b, c, combination⟩ := fan.exists_coefficients (fan.ray 4)
  have s01 : fan.side 0 (fan.ray 1) = 0 := fan.side_right 0
  have s40 : fan.side 4 (fan.ray 0) = 0 := fan.side_right 4
  have s02 := fan.side_strict 0 2 (by decide) (by decide)
  have s04 := fan.side_strict 0 4 (by decide) (by decide)
  have s41 := fan.side_strict 4 1 (by decide) (by decide)
  have s42 := fan.side_strict 4 2 (by decide) (by decide)
  have first := congrArg (fan.side 0) combination
  have last := congrArg (fan.side 4) combination
  simp only [map_add, map_smul, smul_eq_mul, fan.side_left,
    s01, s40, mul_zero, zero_add, add_zero] at first last
  have cp : 0 < c := by
    by_contra h
    have := mul_nonneg_of_nonpos_of_nonpos (not_lt.mp h) s02.le
    nlinarith
  have bn : b < 0 := by
    by_contra h
    have := mul_nonpos_of_nonneg_of_nonpos (not_lt.mp h) s41.le
    nlinarith [mul_neg_of_pos_of_neg cp s42]
  exact ⟨a, b, c, bn, cp, fan.coefficient_sum (fan.level 4) combination, combination⟩

/-- The first supporting line has the expected one-parameter description. -/
theorem first_side_line (fan : FiveRayFan) {x : Space}
    (level : fan.height x = 1) (on_side : fan.side 0 x = 0) :
    ∃ t : ℝ, x = AffineMap.lineMap (fan.ray 0) (fan.ray 1) t := by
  obtain ⟨a, b, c, combination⟩ := fan.exists_coefficients x
  have total := fan.coefficient_sum level combination
  have s01 : fan.side 0 (fan.ray 1) = 0 := fan.side_right 0
  have s02 := fan.side_strict 0 2 (by decide) (by decide)
  have measured := congrArg (fan.side 0) combination
  simp only [map_add, map_smul, smul_eq_mul, fan.side_left, s01, on_side,
    mul_zero, zero_add] at measured
  have cz : c = 0 := (mul_eq_zero.mp measured).resolve_right s02.ne
  have ae : a = 1 - b := by linarith
  refine ⟨b, ?_⟩
  rw [← combination, cz, ae, zero_smul, add_zero, AffineMap.lineMap_apply_module]

end SixVertexUnfolding.FiveRayFan
