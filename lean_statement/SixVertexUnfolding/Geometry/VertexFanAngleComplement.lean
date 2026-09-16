import SixVertexUnfolding.Geometry.VertexFanPointAngles

/-! The two angular routes between surface points add to the total angle. -/

namespace SixVertexUnfolding.ConvexPolyhedron.VertexFaceFan

open Real

variable {P : ConvexPolyhedron} {pole : P.Vertex} {n : ℕ} [NeZero n]
  (fan : P.VertexFaceFan pole n)

theorem openingAngle_complement (few : n = 3 ∨ n = 4 ∨ n = 5) (a b : Fin n) (different : a ≠ b) :
    fan.openingAngle a (b - a).castSucc + fan.openingAngle b (a - b).castSucc = fan.totalAngle := by
  rcases few with rfl | rfl | rfl
  all_goals
    fin_cases a <;> fin_cases b <;>
      simp_all [openingAngle, Fin.partialSum, List.ofFn_succ, totalAngle,
        Fin.sum_univ_succ, Fin.neg_def] <;> ring

theorem first_angle_le_later_start (a b : Fin n) (different : a ≠ b) :
    fan.sectorAngle a ≤ fan.openingAngle a (b - a).castSucc := by
  have later : (1 : Fin (n + 1)) ≤ (b - a).castSucc := by
    have nonzero : b - a ≠ 0 := sub_ne_zero.mpr different.symm
    have val_nonzero : (b - a).val ≠ 0 := fun h => nonzero (Fin.ext h)
    change 1 % (n + 1) ≤ (b - a).val
    rw [Nat.mod_eq_of_lt (by have := NeZero.pos n; omega)]
    omega
  have step := fan.openingAngle_step a (0 : Fin n)
  have first : (Fin.succ (0 : Fin n)) = (1 : Fin (n + 1)) := by
    apply Fin.ext
    change 1 = 1 % (n + 1)
    exact (Nat.mod_eq_of_lt (by have := NeZero.pos n; omega)).symm
  simp only [first, Fin.castSucc_zero, fan.openingAngle_zero, add_zero, sub_zero] at step
  rw [← step]
  exact (fan.openingAngle_strictMono a).monotone later

theorem complementary_point_angles (few : n = 3 ∨ n = 4 ∨ n = 5) (a b : Fin n) (different : a ≠ b)
    (x y : ℝ) (hx : 0 ≤ x ∧ x ≤ fan.sectorAngle a) (hy : 0 ≤ y ∧ y ≤ fan.sectorAngle b) :
    let first := fan.openingAngle a (b - a).castSucc + y - x
    let second := fan.openingAngle b (a - b).castSucc + x - y
    0 ≤ first ∧ 0 ≤ second ∧ first + second = fan.totalAngle := by
  dsimp
  have left := fan.first_angle_le_later_start a b different
  have right := fan.first_angle_le_later_start b a different.symm
  have complement := fan.openingAngle_complement few a b different
  exact ⟨by linarith [hx.2, hy.1], by linarith [hy.2, hx.1], by linarith⟩

end SixVertexUnfolding.ConvexPolyhedron.VertexFaceFan
