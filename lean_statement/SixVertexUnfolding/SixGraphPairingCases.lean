import Mathlib

/-! Propositional case analysis for six vertices; no graph or geometry is assumed here. -/

namespace SixVertexUnfolding.SmallGraphs

set_option maxHeartbeats 1000000 in
/-- The fifteen possible pairings or the ten possible separated triple partitions exhaust the degree-one-or-two cases. -/
theorem six_pairing_propositional_cases
    (e01 e02 e03 e04 e05 e12 e13 e14 e15 e23 e24 e25 e34 e35 e45 : Prop)
    (nonisolated : (e01 ∨ e02 ∨ e03 ∨ e04 ∨ e05) ∧
      (e01 ∨ e12 ∨ e13 ∨ e14 ∨ e15) ∧
      (e02 ∨ e12 ∨ e23 ∨ e24 ∨ e25) ∧
      (e03 ∨ e13 ∨ e23 ∨ e34 ∨ e35) ∧
      (e04 ∨ e14 ∨ e24 ∨ e34 ∨ e45) ∧
      (e05 ∨ e15 ∨ e25 ∨ e35 ∨ e45))
    (bounded : ¬ (e01 ∧ e02 ∧ e03) ∧
      ¬ (e01 ∧ e02 ∧ e04) ∧
      ¬ (e01 ∧ e02 ∧ e05) ∧
      ¬ (e01 ∧ e03 ∧ e04) ∧
      ¬ (e01 ∧ e03 ∧ e05) ∧
      ¬ (e01 ∧ e04 ∧ e05) ∧
      ¬ (e02 ∧ e03 ∧ e04) ∧
      ¬ (e02 ∧ e03 ∧ e05) ∧
      ¬ (e02 ∧ e04 ∧ e05) ∧
      ¬ (e03 ∧ e04 ∧ e05) ∧
      ¬ (e01 ∧ e12 ∧ e13) ∧
      ¬ (e01 ∧ e12 ∧ e14) ∧
      ¬ (e01 ∧ e12 ∧ e15) ∧
      ¬ (e01 ∧ e13 ∧ e14) ∧
      ¬ (e01 ∧ e13 ∧ e15) ∧
      ¬ (e01 ∧ e14 ∧ e15) ∧
      ¬ (e12 ∧ e13 ∧ e14) ∧
      ¬ (e12 ∧ e13 ∧ e15) ∧
      ¬ (e12 ∧ e14 ∧ e15) ∧
      ¬ (e13 ∧ e14 ∧ e15) ∧
      ¬ (e02 ∧ e12 ∧ e23) ∧
      ¬ (e02 ∧ e12 ∧ e24) ∧
      ¬ (e02 ∧ e12 ∧ e25) ∧
      ¬ (e02 ∧ e23 ∧ e24) ∧
      ¬ (e02 ∧ e23 ∧ e25) ∧
      ¬ (e02 ∧ e24 ∧ e25) ∧
      ¬ (e12 ∧ e23 ∧ e24) ∧
      ¬ (e12 ∧ e23 ∧ e25) ∧
      ¬ (e12 ∧ e24 ∧ e25) ∧
      ¬ (e23 ∧ e24 ∧ e25) ∧
      ¬ (e03 ∧ e13 ∧ e23) ∧
      ¬ (e03 ∧ e13 ∧ e34) ∧
      ¬ (e03 ∧ e13 ∧ e35) ∧
      ¬ (e03 ∧ e23 ∧ e34) ∧
      ¬ (e03 ∧ e23 ∧ e35) ∧
      ¬ (e03 ∧ e34 ∧ e35) ∧
      ¬ (e13 ∧ e23 ∧ e34) ∧
      ¬ (e13 ∧ e23 ∧ e35) ∧
      ¬ (e13 ∧ e34 ∧ e35) ∧
      ¬ (e23 ∧ e34 ∧ e35) ∧
      ¬ (e04 ∧ e14 ∧ e24) ∧
      ¬ (e04 ∧ e14 ∧ e34) ∧
      ¬ (e04 ∧ e14 ∧ e45) ∧
      ¬ (e04 ∧ e24 ∧ e34) ∧
      ¬ (e04 ∧ e24 ∧ e45) ∧
      ¬ (e04 ∧ e34 ∧ e45) ∧
      ¬ (e14 ∧ e24 ∧ e34) ∧
      ¬ (e14 ∧ e24 ∧ e45) ∧
      ¬ (e14 ∧ e34 ∧ e45) ∧
      ¬ (e24 ∧ e34 ∧ e45) ∧
      ¬ (e05 ∧ e15 ∧ e25) ∧
      ¬ (e05 ∧ e15 ∧ e35) ∧
      ¬ (e05 ∧ e15 ∧ e45) ∧
      ¬ (e05 ∧ e25 ∧ e35) ∧
      ¬ (e05 ∧ e25 ∧ e45) ∧
      ¬ (e05 ∧ e35 ∧ e45) ∧
      ¬ (e15 ∧ e25 ∧ e35) ∧
      ¬ (e15 ∧ e25 ∧ e45) ∧
      ¬ (e15 ∧ e35 ∧ e45) ∧
      ¬ (e25 ∧ e35 ∧ e45)) :
    ((e01 ∧ e23 ∧ e45) ∨
      (e01 ∧ e24 ∧ e35) ∨
      (e01 ∧ e25 ∧ e34) ∨
      (e02 ∧ e13 ∧ e45) ∨
      (e02 ∧ e14 ∧ e35) ∨
      (e02 ∧ e15 ∧ e34) ∨
      (e03 ∧ e12 ∧ e45) ∨
      (e03 ∧ e14 ∧ e25) ∨
      (e03 ∧ e15 ∧ e24) ∨
      (e04 ∧ e12 ∧ e35) ∨
      (e04 ∧ e13 ∧ e25) ∨
      (e04 ∧ e15 ∧ e23) ∨
      (e05 ∧ e12 ∧ e34) ∨
      (e05 ∧ e13 ∧ e24) ∨
      (e05 ∧ e14 ∧ e23)) ∨
    ((¬ e03 ∧ ¬ e04 ∧ ¬ e05 ∧ ¬ e13 ∧ ¬ e14 ∧ ¬ e15 ∧ ¬ e23 ∧ ¬ e24 ∧ ¬ e25) ∨
      (¬ e02 ∧ ¬ e04 ∧ ¬ e05 ∧ ¬ e12 ∧ ¬ e14 ∧ ¬ e15 ∧ ¬ e23 ∧ ¬ e34 ∧ ¬ e35) ∨
      (¬ e02 ∧ ¬ e03 ∧ ¬ e05 ∧ ¬ e12 ∧ ¬ e13 ∧ ¬ e15 ∧ ¬ e24 ∧ ¬ e34 ∧ ¬ e45) ∨
      (¬ e02 ∧ ¬ e03 ∧ ¬ e04 ∧ ¬ e12 ∧ ¬ e13 ∧ ¬ e14 ∧ ¬ e25 ∧ ¬ e35 ∧ ¬ e45) ∨
      (¬ e01 ∧ ¬ e04 ∧ ¬ e05 ∧ ¬ e12 ∧ ¬ e24 ∧ ¬ e25 ∧ ¬ e13 ∧ ¬ e34 ∧ ¬ e35) ∨
      (¬ e01 ∧ ¬ e03 ∧ ¬ e05 ∧ ¬ e12 ∧ ¬ e23 ∧ ¬ e25 ∧ ¬ e14 ∧ ¬ e34 ∧ ¬ e45) ∨
      (¬ e01 ∧ ¬ e03 ∧ ¬ e04 ∧ ¬ e12 ∧ ¬ e23 ∧ ¬ e24 ∧ ¬ e15 ∧ ¬ e35 ∧ ¬ e45) ∨
      (¬ e01 ∧ ¬ e02 ∧ ¬ e05 ∧ ¬ e13 ∧ ¬ e23 ∧ ¬ e35 ∧ ¬ e14 ∧ ¬ e24 ∧ ¬ e45) ∨
      (¬ e01 ∧ ¬ e02 ∧ ¬ e04 ∧ ¬ e13 ∧ ¬ e23 ∧ ¬ e34 ∧ ¬ e15 ∧ ¬ e25 ∧ ¬ e45) ∨
      (¬ e01 ∧ ¬ e02 ∧ ¬ e03 ∧ ¬ e14 ∧ ¬ e24 ∧ ¬ e34 ∧ ¬ e15 ∧ ¬ e25 ∧ ¬ e35)) := by
  grind (splits := 64)

end SixVertexUnfolding.SmallGraphs
