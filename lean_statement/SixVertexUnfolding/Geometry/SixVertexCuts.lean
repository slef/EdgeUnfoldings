import SixVertexUnfolding.Geometry.ThreeConnectivity

/-! Three-connectivity excludes separating the four surviving vertices into two pairs. -/

namespace SixVertexUnfolding.SmallGraphs

/-- A label constant along every edge is constant on a connected graph. -/
theorem label_constant_on_connected {V A : Type*} (G : SimpleGraph V) (connected : G.Connected)
    (label : V → A) (along_edges : ∀ a b, G.Adj a b → label a = label b) (a b : V) :
    label a = label b := by
  obtain ⟨walk⟩ := connected a b
  induction walk with
  | nil => rfl
  | cons edge rest induction => exact (along_edges _ _ edge).trans induction

end SixVertexUnfolding.SmallGraphs

namespace SixVertexUnfolding.ConvexPolyhedron

/-- After deleting the last two of six vertices, an original edge crosses either partition into pairs. -/
theorem six_vertices_have_cross_edge (P : ConvexPolyhedron) (index : Fin 6 ≃ P.Vertex) :
    P.edgeGraph.Adj (index 0) (index 2) ∨ P.edgeGraph.Adj (index 0) (index 3) ∨
      P.edgeGraph.Adj (index 1) (index 2) ∨ P.edgeGraph.Adj (index 1) (index 3) := by
  classical
  by_contra none
  push Not at none
  let deleted : Finset P.Vertex := {index 4, index 5}
  let remain := {v : P.Vertex | v ∉ deleted}
  let graph := P.edgeGraph.induce remain
  let label (v : remain) : Bool := decide ((index.symm v.val : Fin 6) < 2)
  have connected : graph.Connected := P.edgeGraph_three_connected deleted (by
    simp [deleted, index.injective.eq_iff])
  have survives (i : Fin 6) (i4 : i ≠ 4) (i5 : i ≠ 5) : index i ∈ remain := by
    simp [remain, deleted, index.injective.eq_iff, i4, i5]
  let first : remain := ⟨index 0, survives 0 (by decide) (by decide)⟩
  let second : remain := ⟨index 2, survives 2 (by decide) (by decide)⟩
  have no_forward (i j : Fin 6) (first_pair : i < 2) (second_pair : 2 ≤ j) (small : j < 4) :
      ¬ P.edgeGraph.Adj (index i) (index j) := by
    have left : i = 0 ∨ i = 1 := by omega
    have right : j = 2 ∨ j = 3 := by omega
    rcases left with rfl | rfl <;> rcases right with rfl | rfl
    exacts [none.1, none.2.1, none.2.2.1, none.2.2.2]
  have along_edges (a b : remain) (edge : graph.Adj a b) : label a = label b := by
    obtain ⟨i, ai⟩ := index.surjective a.val
    obtain ⟨j, bj⟩ := index.surjective b.val
    have a_remains : i ≠ 4 ∧ i ≠ 5 := by
      have member := a.property
      change a.val ∉ deleted at member
      simpa [deleted, ← ai, index.injective.eq_iff] using member
    have b_remains : j ≠ 4 ∧ j ≠ 5 := by
      have member := b.property
      change b.val ∉ deleted at member
      simpa [deleted, ← bj, index.injective.eq_iff] using member
    have original : P.edgeGraph.Adj (index i) (index j) := by
      rw [ai, bj]
      exact edge
    change decide (index.symm a.val < 2) = decide (index.symm b.val < 2)
    rw [← ai, ← bj, index.symm_apply_apply, index.symm_apply_apply]
    have i_small : i < 4 := by omega
    have j_small : j < 4 := by omega
    by_cases left : i < 2
    · by_cases right : j < 2
      · simp [left, right]
      · exact False.elim (no_forward i j left (by omega) j_small original)
    · by_cases right : j < 2
      · exact False.elim (no_forward j i right (by omega) i_small original.symm)
      · simp [left, right]
  have impossible := SmallGraphs.label_constant_on_connected graph connected label along_edges first second
  norm_num [label, first, second] at impossible
  exact (by decide : (2 : Fin 6) ≠ 0) impossible

/-- Four complementary edges cannot separate four surviving vertices into two pairs. -/
theorem no_complement_square (P : ConvexPolyhedron) (index : Fin 6 ≃ P.Vertex) :
    ¬ (P.edgeGraphᶜ.Adj (index 0) (index 2) ∧ P.edgeGraphᶜ.Adj (index 0) (index 3) ∧
      P.edgeGraphᶜ.Adj (index 1) (index 2) ∧ P.edgeGraphᶜ.Adj (index 1) (index 3)) := by
  rintro ⟨first, second, third, fourth⟩
  rcases P.six_vertices_have_cross_edge index with edge | edge | edge | edge
  exacts [first.2 edge, second.2 edge, third.2 edge, fourth.2 edge]

end SixVertexUnfolding.ConvexPolyhedron
