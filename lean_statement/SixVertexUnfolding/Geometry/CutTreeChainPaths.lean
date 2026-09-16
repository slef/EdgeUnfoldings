import SixVertexUnfolding.Geometry.CutTreeChainSeparation
import SixVertexUnfolding.Geometry.TreeEdgeConnector

/-! Convert the simple path between two actual tree edges into the
finite chain used by the geometric separation proof. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set SimpleGraph

namespace CutTreeChain

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a}
    {u v w z : T.vertices} (first : T.graph.Adj u v) (middle : T.graph.Walk v w)
    (last : T.graph.Adj w z)

/-- The vertices and edges of an actual simple path, indexed consecutively. -/
def ofPath (simple : (Walk.cons first (middle.concat last)).IsPath) :
    CutTreeChain T middle.length where
  vertex i := (Walk.cons first (middle.concat last)).getVert i.val
  simple := by
    intro i j same
    apply Fin.ext
    apply simple.getVert_injOn _ _ same <;>
      simp only [Set.mem_setOf_eq, Walk.length_cons, Walk.length_concat] <;> omega
  edge i := (Walk.cons first (middle.concat last)).adj_getVert_succ (by
    simpa only [Walk.length_cons, Walk.length_concat, Nat.add_assoc] using i.isLt)

theorem ofPath_first_edge (simple : (Walk.cons first (middle.concat last)).IsPath) :
    ((ofPath first middle last simple).dart 0).edge = s(u, v) := by
  simp [dart, ofPath, Walk.getVert_cons_succ, SimpleGraph.Dart.edge]

theorem ofPath_last_edge (simple : (Walk.cons first (middle.concat last)).IsPath) :
    ((ofPath first middle last simple).dart (Fin.last middle.length).succ).edge = s(w, z) := by
  have near : (middle.concat last).getVert middle.length = w := by
    simp [Walk.concat_eq_append, Walk.getVert_append]
  have far : (middle.concat last).getVert (middle.length + 1) = z := by
    simpa only [Walk.length_concat] using (middle.concat last).getVert_length
  change s((Walk.cons first (middle.concat last)).getVert (middle.length + 1),
    (Walk.cons first (middle.concat last)).getVert (middle.length + 1 + 1)) = _
  rw [Walk.getVert_cons_succ, Walk.getVert_cons_succ, near, far]

end CutTreeChain

namespace CutTreeCharts

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a} (charts : CutTreeCharts T)

/-- The global kite depends only on the unoriented tree edge. -/
theorem kite_eq_of_same_edge {u v w z : T.vertices} (first : T.graph.Adj u v)
    (last : T.graph.Adj w z) (same : s(u, v) = s(w, z)) :
    charts.kite first = charts.kite last := by
  rcases Sym2.eq_iff.mp same with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact charts.kite_reverse first

end CutTreeCharts

namespace CutLocusTree

variable {P : ConvexPolyhedron} {a : frontier P.body} (T : P.CutLocusTree a)

/-- Any distinct pair of actual edges occurs as the end edges of one simple chain. -/
theorem exists_chain_between_edges {u v w z : T.vertices} (first : T.graph.Adj u v)
    (last : T.graph.Adj w z) (different : s(u, v) ≠ s(w, z)) :
    ∃ n : ℕ, ∃ chain : CutTreeChain T n,
      (chain.dart 0).edge = s(u, v) ∧ (chain.dart (Fin.last n).succ).edge = s(w, z) := by
  obtain ⟨start, next, near, far, first', last', middle, first_same, last_same, simple⟩ :=
    TreeFrames.exists_edge_to_edge_path T.tree first last different
  refine ⟨middle.length, CutTreeChain.ofPath first' middle last' simple, ?_, ?_⟩
  · exact (CutTreeChain.ofPath_first_edge first' middle last' simple).trans first_same
  · exact (CutTreeChain.ofPath_last_edge first' middle last' simple).trans last_same

end CutLocusTree
end SixVertexUnfolding.ConvexPolyhedron
