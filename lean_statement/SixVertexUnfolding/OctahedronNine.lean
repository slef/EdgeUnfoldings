import SixVertexUnfolding.Octahedron
import SixVertexUnfolding.Geometry.OctahedralJunctionTriangles

/-! Nineteen pairs are already safe. These are the nine remaining geometric comparisons. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

/-- The three slit pairs, two opposite petal pairs, and four remote fan/petal pairs.
`false` denotes a fan triangle; `true` denotes a petal. -/
structure RemainingNine : Prop where
  slit_petals : net.Separated (true, 0) (true, 3)
  slit_left : net.Separated (true, 0) (false, 3)
  slit_right : net.Separated (true, 3) (false, 0)
  opposite_even : net.Separated (true, 0) (true, 2)
  opposite_odd : net.Separated (true, 1) (true, 3)
  remote : ∀ i : Fin 4, net.Separated (true, i) (false, i + 2)

set_option maxHeartbeats 2000000 in
/-- The original-edge certificate now needs only nine geometric comparisons. -/
theorem hasEdgeUnfolding_of_nine_comparisons (octahedral : graph.kind = .octahedron)
    (remaining : net.RemainingNine) : P.HasEdgeUnfolding := by
  apply net.hasEdgeUnfolding_of_remaining_pairs octahedral
  · intro i j different
    change net.Separated (false, i) (true, j)
    fin_cases i <;> fin_cases j
    · exact False.elim (different rfl)
    · exact net.neighboring_fan_petal 0
    · exact (remaining.remote 2).symm
    · exact remaining.slit_right.symm
    · exact (net.neighboring_petal_fan 0).symm
    · exact False.elim (different rfl)
    · exact net.neighboring_fan_petal 1
    · exact (remaining.remote 3).symm
    · exact (remaining.remote 0).symm
    · exact (net.neighboring_petal_fan 1).symm
    · exact False.elim (different rfl)
    · exact net.neighboring_fan_petal 2
    · exact remaining.slit_left.symm
    · exact (remaining.remote 1).symm
    · exact (net.neighboring_petal_fan 2).symm
    · exact False.elim (different rfl)
  · intro i j different
    change net.Separated (true, i) (true, j)
    fin_cases i <;> fin_cases j
    · exact False.elim (different rfl)
    · exact net.neighboring_petals 0
    · exact remaining.opposite_even
    · exact remaining.slit_petals
    · exact (net.neighboring_petals 0).symm
    · exact False.elim (different rfl)
    · exact net.neighboring_petals 1
    · exact remaining.opposite_odd
    · exact remaining.opposite_even.symm
    · exact (net.neighboring_petals 1).symm
    · exact False.elim (different rfl)
    · exact net.neighboring_petals 2
    · exact remaining.slit_petals.symm
    · exact remaining.opposite_odd.symm
    · exact (net.neighboring_petals 2).symm
    · exact False.elim (different rfl)

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
