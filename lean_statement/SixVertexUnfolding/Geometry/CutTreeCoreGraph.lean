import SixVertexUnfolding.Geometry.CutTreeCharts

/-! Removing the original leaf vertices leaves a connected graph.
Every cut-tree edge has at least one retained endpoint, because a solid
has at least three nonsource original vertices. -/

namespace SixVertexUnfolding.ConvexPolyhedron.CutLocusTree

open Set

variable {P : ConvexPolyhedron} {a : frontier P.body} (T : P.CutLocusTree a)

/-- There is a third cut-tree vertex outside any given pair. -/
theorem exists_vertex_outside_pair (u v : T.vertices) : ∃ w : T.vertices, w ≠ u ∧ w ≠ v := by
  classical
  have not_subset : ¬ P.vertices ⊆ ({(a : Space), (u : Space), (v : Space)} : Finset Space) := by
    intro subset
    have bound := (Finset.card_le_card subset).trans Finset.card_le_three
    have lower := P.four_le_vertex_count
    omega
  obtain ⟨w, original, outside⟩ := Finset.not_subset.mp not_subset
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at outside
  let z : T.vertices := ⟨w, T.toEmbeddedCutGraph.original_vertex_mem original outside.1⟩
  exact ⟨z, fun same => outside.2.1 (congrArg Subtype.val same),
    fun same => outside.2.2 (congrArg Subtype.val same)⟩

/-- Two original leaves cannot be adjacent in this cut tree. -/
theorem edge_has_nonvertex_endpoint (charts : CutTreeCharts T) {u v : T.vertices}
    (edge : T.graph.Adj u v) : (u : Space) ∉ P.vertices ∨ (v : Space) ∉ P.vertices := by
  by_contra neither
  push Not at neither
  have only_u : ∀ w, T.graph.Adj u w → w = v := fun w hw =>
    (charts.original_leaves u neither.1).unique hw edge
  have only_v : ∀ w, T.graph.Adj v w → w = u := fun w hw =>
    (charts.original_leaves v neither.2).unique hw edge.symm
  have stays : ∀ {x y : T.vertices}, T.graph.Walk x y → x = u ∨ x = v → y = u ∨ y = v := by
    intro x y walk
    induction walk with
    | nil => exact fun hx => hx
    | @cons x y z first rest ih =>
      intro hx
      apply ih
      rcases hx with rfl | rfl
      · exact Or.inr (only_u y first)
      · exact Or.inl (only_v y first)
  obtain ⟨w, wu, wv⟩ := T.exists_vertex_outside_pair u v
  obtain ⟨walk⟩ := T.tree.connected u w
  exact (stays walk (Or.inl rfl)).elim wu wv

/-- All retained cut-tree vertices can still be joined after deleting the original leaves. -/
theorem nonvertex_graph_preconnected (charts : CutTreeCharts T) :
    (T.graph.induce {u : T.vertices | (u : Space) ∉ P.vertices}).Preconnected := by
  apply T.tree.connected.preconnected.induce_of_degree_eq_one
  intro u outside
  have original : (u : Space) ∈ P.vertices := by simpa only [mem_setOf_eq, not_not] using outside
  intro v hv w hw
  exact (charts.original_leaves u original).unique hv hw

end SixVertexUnfolding.ConvexPolyhedron.CutLocusTree
