import SixVertexUnfolding.Geometry.CutGraphAcyclic
import SixVertexUnfolding.Geometry.VoronoiChartNotLeaf

/-! Every leaf of the actual cut-locus tree is an original polyhedron
vertex. Regular cut points and junctions are both excluded by local geometry. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- An embedded cut-graph vertex with exactly one neighbor must be an original vertex. -/
theorem cut_graph_leaf_is_vertex (a : frontier P.body) (K : P.EmbeddedCutGraph a)
    (u v : K.vertices) (edge : K.graph.Adj u v)
    (only_neighbor : ∀ w, K.graph.Adj u w → w = v) : (u : Space) ∈ P.vertices := by
  by_contra not_vertex
  obtain ⟨b, cut, at_u⟩ := K.vertex_in_trace u
  have different : a ≠ b := by rintro rfl; exact P.source_not_cutSet a cut
  have nonvertex : (b : Space) ∉ P.vertices := by simpa only [at_u] using not_vertex
  by_cases junction : b ∈ P.junctions a
  · have many := (graph.junction_iff_route_count small_faces a b different).mp junction
    obtain ⟨chart⟩ := graph.cut_voronoi_chart small_faces a b different nonvertex
    obtain ⟨U, openU, uU, local_segment⟩ := K.leaf_segment_neighborhood u v only_neighbor
    obtain ⟨F, cofacial⟩ := K.cofacial_edges u v edge
    apply chart.junction_not_one_sided different many v F (by simpa only [at_u] using cofacial)
      U openU (by simpa only [at_u] using uU)
    intro x hx near multiple
    simpa only [at_u] using
      local_segment ⟨near, ⟨⟨chart.map x, chart.on_surface hx⟩, Or.inl multiple, rfl⟩⟩
  · have regular : b ∉ P.cutExceptions a := by
      rintro (branch | vertex)
      · exact junction branch
      · exact nonvertex vertex.1
    obtain ⟨arc⟩ := graph.regular_cut_arc small_faces a b cut regular
    exact K.cut_arc_not_leaf u v edge (by simpa only [at_u] using arc) only_neighbor

include graph small_faces in
/-- The usual degree-one formulation of the cut-tree leaf theorem. -/
theorem cut_graph_degree_one_is_vertex (a : frontier P.body) (K : P.EmbeddedCutGraph a)
    (u : K.vertices) [Fintype (K.graph.neighborSet u)] (leaf : K.graph.degree u = 1) :
    (u : Space) ∈ P.vertices := by
  obtain ⟨v, edge, unique⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp leaf
  exact graph.cut_graph_leaf_is_vertex small_faces a K u v edge unique

include graph small_faces in
/-- The canonical models have an exact finite cut tree whose leaves are original vertices. -/
theorem exists_cut_tree_with_vertex_leaves (a : frontier P.body) :
    ∃ K : P.EmbeddedCutGraph a, K.graph.IsTree ∧ ∀ u v : K.vertices,
      K.graph.Adj u v → (∀ w, K.graph.Adj u w → w = v) → (u : Space) ∈ P.vertices := by
  obtain ⟨K, tree⟩ := graph.exists_cut_tree small_faces a
  exact ⟨K, tree, graph.cut_graph_leaf_is_vertex small_faces a K⟩

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
