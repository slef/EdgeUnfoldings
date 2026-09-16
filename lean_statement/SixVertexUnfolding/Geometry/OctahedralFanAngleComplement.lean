import SixVertexUnfolding.Geometry.OctahedralFanPointAngles

/-! Moving the slit exchanges the two angular routes around the pole.
Their lengths add to the actual total angle at that vertex. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Real

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)

/-- The two complementary sector chains make one complete turn around the vertex. -/
theorem openingAngle_complement (pole : Fin 6) (a b : Fin 4) (different : a ≠ b) :
    graph.openingAngle pole a (b - a).castSucc +
      graph.openingAngle pole b (a - b).castSucc = graph.totalAngleAt pole := by
  rw [← graph.sum_fanAngle]
  fin_cases a <;> fin_cases b <;> simp_all [openingAngle, Fin.sum_univ_four, Fin.neg_def] <;> ring

/-- A sector strictly later than the slit begins beyond the first sector's full angle. -/
theorem first_angle_le_later_start (pole : Fin 6) (a b : Fin 4) (different : a ≠ b) :
    graph.fanAngle pole a ≤ graph.openingAngle pole a (b - a).castSucc := by
  have later : (1 : Fin 5) ≤ (b - a).castSucc := by
    have nonzero : b - a ≠ 0 := sub_ne_zero.mpr different.symm
    have val_nonzero : (b - a).val ≠ 0 := fun h => nonzero (Fin.ext h)
    change 1 ≤ (b - a).val
    omega
  exact (graph.openingAngle_strictMono pole a).monotone later

/-- Offsets within two different sectors give two nonnegative complementary angular distances. -/
theorem complementary_point_angles (pole : Fin 6) (a b : Fin 4) (different : a ≠ b)
    (x y : ℝ) (hx : 0 ≤ x ∧ x ≤ graph.fanAngle pole a)
    (hy : 0 ≤ y ∧ y ≤ graph.fanAngle pole b) :
    let first := graph.openingAngle pole a (b - a).castSucc + y - x
    let second := graph.openingAngle pole b (a - b).castSucc + x - y
    0 ≤ first ∧ 0 ≤ second ∧ first + second = graph.totalAngleAt pole := by
  dsimp
  have left := graph.first_angle_le_later_start pole a b different
  have right := graph.first_angle_le_later_start pole b a different.symm
  have complement := graph.openingAngle_complement pole a b different
  exact ⟨by linarith [hx.2, hy.1], by linarith [hy.2, hx.1], by linarith⟩

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
