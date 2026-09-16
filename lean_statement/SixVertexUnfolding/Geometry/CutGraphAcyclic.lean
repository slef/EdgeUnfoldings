import SixVertexUnfolding.Geometry.EdgeLiftPotential
import SixVertexUnfolding.Geometry.CutSetContractible
import SixVertexUnfolding.Geometry.ConnectedCutGraph

/-! The cut graph is acyclic. A return path avoiding a selected edge would
contradict the real potential obtained by lifting that edge's circle map. -/

namespace SixVertexUnfolding

open Set

/-- A potential changing on just one edge proves that removing the edge separates its endpoints. -/
theorem bridge_of_edge_potential {V : Type*} (G : SimpleGraph V) (u v : V)
    (edge : G.Adj u v) (height : V → ℝ) (increment : height v = height u + 1)
    (constant : ∀ p q, G.Adj p q → s(p, q) ≠ s(u, v) → height p = height q) : G.IsBridge s(u, v) := by
  apply SimpleGraph.isBridge_iff.mpr
  refine ⟨edge, ?_⟩
  rintro ⟨walk⟩
  have same : ∀ {p q : V}, (G.deleteEdges {s(u, v)}).Walk p q → height p = height q := by
    intro p q path
    induction path with
    | nil => rfl
    | @cons p q r adj tail ih =>
      have allowed := SimpleGraph.deleteEdges_adj.mp adj
      exact (constant p q allowed.1 (by simpa only [mem_singleton_iff] using allowed.2)).trans ih
  have equal := same walk
  linarith

namespace ConvexPolyhedron.EmbeddedCutGraph

variable {P : ConvexPolyhedron} {a : frontier P.body} (K : P.EmbeddedCutGraph a)

/-- A finite embedded graph with contractible actual trace has no graph cycle. -/
theorem acyclic_of_contractible_trace [ContractibleSpace (P.cutSetInSpace a)] : K.graph.IsAcyclic := by
  apply SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mpr
  intro u v edge
  obtain ⟨height, increment, constant⟩ := K.exists_edge_potential u v edge
  exact bridge_of_edge_potential K.graph u v edge height increment constant

end ConvexPolyhedron.EmbeddedCutGraph

namespace ConvexPolyhedron.SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- The exact finite cut graph of a canonical model is a tree. -/
theorem embedded_cut_graph_isTree (a : frontier P.body) (K : P.EmbeddedCutGraph a) : K.graph.IsTree := by
  letI : ContractibleSpace (P.cutSetInSpace a) := graph.cutSetInSpace_contractible small_faces a
  exact ⟨graph.embedded_cut_graph_connected small_faces a K, K.acyclic_of_contractible_trace⟩

include graph small_faces in
/-- A finite embedded cut-locus tree exists for every source in a canonical model. -/
theorem exists_cut_tree (a : frontier P.body) : ∃ K : P.EmbeddedCutGraph a, K.graph.IsTree := by
  obtain ⟨K⟩ := graph.exists_embedded_cut_graph small_faces a
  exact ⟨K, graph.embedded_cut_graph_isTree small_faces a K⟩

end ConvexPolyhedron.SixVertexGraph
end SixVertexUnfolding
