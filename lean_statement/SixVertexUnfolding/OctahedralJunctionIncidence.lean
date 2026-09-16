import SixVertexUnfolding.OctahedralAngleIncidence

/-! The four corners meeting at an equator junction are exactly its complete vertex link. -/

namespace SixVertexUnfolding.OctahedralTriangles

set_option maxHeartbeats 3000000 in
theorem junction_angle_incidence (quantity : Fin 6 → Fin 6 → Fin 6 → ℝ)
    (symmetric : ∀ a b c, quantity a b c = quantity c b a) (source : Fin 6) (sector : Fin 4) :
    quantity source (fanNeighbor source (sector + 1)) (fanNeighbor source sector) +
      quantity (fanNeighbor source sector) (fanNeighbor source (sector + 1)) (opposite source) +
      quantity (opposite source) (fanNeighbor source (sector + 1)) (fanNeighbor source (sector + 2)) +
      quantity (fanNeighbor source (sector + 2)) (fanNeighbor source (sector + 1)) source =
        ∑ i : Fin 4, quantity (fanNeighbor (fanNeighbor source (sector + 1)) i)
          (fanNeighbor source (sector + 1)) (fanNeighbor (fanNeighbor source (sector + 1)) (i + 1)) := by
  fin_cases source <;> fin_cases sector <;>
    simp [fanNeighbor, opposite, Fin.sum_univ_succ] <;>
    simp only [symmetric, add_comm, add_left_comm, add_assoc] <;> ring

end SixVertexUnfolding.OctahedralTriangles
