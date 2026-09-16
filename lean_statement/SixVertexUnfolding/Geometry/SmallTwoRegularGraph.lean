import SixVertexUnfolding.Definitions

/-! Two disjoint components with two neighbors at every vertex would
need at least six vertices. This elementary bound identifies the five-vertex link. -/

namespace SixVertexUnfolding

/-- A nonempty graph on at most five vertices with two neighbors everywhere is connected. -/
theorem small_two_neighbor_graph_connected {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (small : Fintype.card V ≤ 5)
    (neighbors : ∀ u, ∃ a b, a ≠ b ∧ G.neighborSet u = {a, b}) : G.Connected := by
  classical
  refine { preconnected := ?_ }
  intro u v
  by_contra disconnected
  obtain ⟨a, b, ab, at_u⟩ := neighbors u
  obtain ⟨c, d, cd, at_v⟩ := neighbors v
  have ua : G.Adj u a := by change a ∈ G.neighborSet u; rw [at_u]; simp
  have ub : G.Adj u b := by change b ∈ G.neighborSet u; rw [at_u]; simp
  have vc : G.Adj v c := by change c ∈ G.neighborSet v; rw [at_v]; simp
  have vd : G.Adj v d := by change d ∈ G.neighborSet v; rw [at_v]; simp
  let U : Finset V := {u, a, b}
  let W : Finset V := {v, c, d}
  have threeU : U.card = 3 := by simp [U, ua.ne, ub.ne, ab]
  have threeW : W.card = 3 := by simp [W, vc.ne, vd.ne, cd]
  have reachesU (x : V) (inside : x ∈ U) : G.Reachable u x := by
    rcases (by simpa only [U, Finset.mem_insert, Finset.mem_singleton] using inside :
      x = u ∨ x = a ∨ x = b) with rfl | rfl | rfl
    · exact SimpleGraph.Reachable.rfl
    · exact ua.reachable
    · exact ub.reachable
  have reachesW (x : V) (inside : x ∈ W) : G.Reachable v x := by
    rcases (by simpa only [W, Finset.mem_insert, Finset.mem_singleton] using inside :
      x = v ∨ x = c ∨ x = d) with rfl | rfl | rfl
    · exact SimpleGraph.Reachable.rfl
    · exact vc.reachable
    · exact vd.reachable
  have disjoint : Disjoint U W := Finset.disjoint_left.mpr (fun x xu xw =>
    disconnected ((reachesU x xu).trans (reachesW x xw).symm))
  have bound := Finset.card_le_univ (U ∪ W)
  rw [Finset.card_union_of_disjoint disjoint, threeU, threeW] at bound
  omega

end SixVertexUnfolding
