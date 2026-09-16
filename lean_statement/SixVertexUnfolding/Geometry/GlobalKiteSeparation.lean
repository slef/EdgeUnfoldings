import SixVertexUnfolding.Geometry.CutTreeChainPaths

/-! All distinct kites in the one chosen global development are
nonoverlapping. The numerical budget comes from the actual source cone. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include small_faces

/-- Every distinct pair of tree-edge kites is separated in the fixed common plane. -/
theorem global_kites_nonoverlap {a : frontier P.body} (T : P.CutLocusTree a)
    (charts : CutTreeCharts T) (source : Fin 6)
    (at_source : (a : Space) = (graph.vertex source : Space))
    {u v w z : T.vertices} (first : T.graph.Adj u v) (last : T.graph.Adj w z)
    (different : s(u, v) ≠ s(w, z)) :
    Disjoint (charts.kite first) (interior (charts.kite last)) := by
  obtain ⟨n, chain, first_same, last_same⟩ := T.exists_chain_between_edges first last different
  have first_image : charts.kite (chain.edge 0) = charts.kite first :=
    charts.kite_eq_of_same_edge _ first first_same
  have last_image : charts.kite (chain.edge (Fin.last n).succ) = charts.kite last :=
    charts.kite_eq_of_same_edge _ last last_same
  rw [← first_image, ← last_image]
  exact graph.cut_tree_chain_end_kites_nonoverlap small_faces T charts chain source at_source

/-- Construct the actual, covering chart collection with all its kites separated. -/
theorem exists_separated_cut_tree_charts {a : frontier P.body} (T : P.CutLocusTree a)
    (source : Fin 6) (at_source : (a : Space) = (graph.vertex source : Space))
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val) :
    ∃ charts : CutTreeCharts T,
      ∀ {u v w z : T.vertices} (first : T.graph.Adj u v) (last : T.graph.Adj w z),
        s(u, v) ≠ s(w, z) → Disjoint (charts.kite first) (interior (charts.kite last)) := by
  obtain ⟨charts⟩ := graph.exists_cut_tree_charts small_faces a T cofacial
  exact ⟨charts, fun first last different =>
    graph.global_kites_nonoverlap small_faces T charts source at_source first last different⟩

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
