import SixVertexUnfolding.OctahedralFans

/-! The finite incidence identity relating triangle-corner angles to the four cyclic vertex sectors. -/

namespace SixVertexUnfolding.OctahedralTriangles

set_option maxHeartbeats 2500000 in
/-- Count a symmetric corner quantity either triangle by triangle or around its source vertex. -/
theorem angle_incidence (quantity : Fin 6 → Fin 6 → Fin 6 → ℝ)
    (symmetric : ∀ a b c, quantity a b c = quantity c b a) (v : Fin 6) :
    (∑ t : Fin 8, ∑ i : Fin 3, if corner t i = v then
      quantity (corner t (i + 1)) (corner t i) (corner t (i + 2)) else 0) =
      ∑ i : Fin 4, quantity (fanNeighbor v i) v (fanNeighbor v (i + 1)) := by
  fin_cases v <;>
    simp [corner, fanNeighbor, Fin.sum_univ_succ] <;>
    simp only [symmetric, add_comm, add_left_comm]

end SixVertexUnfolding.OctahedralTriangles
