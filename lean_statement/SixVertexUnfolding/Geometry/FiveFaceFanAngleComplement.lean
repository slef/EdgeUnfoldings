import SixVertexUnfolding.Geometry.FiveFaceFanPointAngles

/-! The two angular routes between surface points add to the total angle. -/

namespace SixVertexUnfolding.ConvexPolyhedron.FiveFaceFan

open Real

variable {P : ConvexPolyhedron} {pole : P.Vertex} (fan : P.FiveFaceFan pole)

theorem openingAngle_complement (a b : Fin 5) (different : a ≠ b) :
    fan.openingAngle a (b - a).castSucc + fan.openingAngle b (a - b).castSucc = fan.totalAngle := by
  fin_cases a <;> fin_cases b <;>
    simp_all [openingAngle, totalAngle, Fin.sum_univ_succ, Fin.neg_def] <;> ring

theorem first_angle_le_later_start (a b : Fin 5) (different : a ≠ b) :
    fan.sectorAngle a ≤ fan.openingAngle a (b - a).castSucc := by
  have later : (1 : Fin 6) ≤ (b - a).castSucc := by
    have nonzero : b - a ≠ 0 := sub_ne_zero.mpr different.symm
    have val_nonzero : (b - a).val ≠ 0 := fun h => nonzero (Fin.ext h)
    change 1 ≤ (b - a).val
    omega
  exact (fan.openingAngle_strictMono a).monotone later

theorem complementary_point_angles (a b : Fin 5) (different : a ≠ b)
    (x y : ℝ) (hx : 0 ≤ x ∧ x ≤ fan.sectorAngle a) (hy : 0 ≤ y ∧ y ≤ fan.sectorAngle b) :
    let first := fan.openingAngle a (b - a).castSucc + y - x
    let second := fan.openingAngle b (a - b).castSucc + x - y
    0 ≤ first ∧ 0 ≤ second ∧ first + second = fan.totalAngle := by
  dsimp
  have left := fan.first_angle_le_later_start a b different
  have right := fan.first_angle_le_later_start b a different.symm
  have complement := fan.openingAngle_complement a b different
  exact ⟨by linarith [hx.2, hy.1], by linarith [hy.2, hx.1], by linarith⟩

end SixVertexUnfolding.ConvexPolyhedron.FiveFaceFan
