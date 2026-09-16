import SixVertexUnfolding.Geometry.UniqueRouteCutVertex
import SixVertexUnfolding.Geometry.JunctionFan

/-! For a source cofacial with every original vertex, all original
nonsource vertices are leaves. Every internal junction therefore has
the flat fan already constructed for the wedge-chain argument. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

namespace EmbeddedCutGraph

/-- At least two original nonsource vertices occur among the cut-graph vertices. -/
theorem vertices_nontrivial {P : ConvexPolyhedron} {a : frontier P.body}
    (K : P.EmbeddedCutGraph a) : Nontrivial K.vertices := by
  classical
  have enough : 1 < (P.vertices.erase (a : Space)).card := by
    have lower := P.four_le_vertex_count
    have bound := Finset.pred_card_le_card_erase (s := P.vertices) (a := (a : Space))
    omega
  obtain ⟨v, hv, w, hw, different⟩ := Finset.one_lt_card.mp enough
  have first := K.original_vertex_mem (Finset.mem_erase.mp hv).2 (Finset.mem_erase.mp hv).1
  have second := K.original_vertex_mem (Finset.mem_erase.mp hw).2 (Finset.mem_erase.mp hw).1
  exact ⟨⟨⟨v, first⟩, ⟨w, second⟩, fun same => different (congrArg Subtype.val same)⟩⟩

end EmbeddedCutGraph

namespace SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- A unique-route cut-tree vertex is a leaf, in the exact one-neighbor sense. -/
theorem unique_route_cut_vertex_is_leaf (a : frontier P.body) (T : P.CutLocusTree a)
    (u : T.vertices) (unique : (P.geodesicFiber a (T.vertexTarget u)).Subsingleton) :
    ∃! v, T.graph.Adj u v := by
  letI : Nontrivial T.vertices := T.toEmbeddedCutGraph.vertices_nontrivial
  obtain ⟨v, edge⟩ := T.tree.connected.preconnected.exists_adj_of_nontrivial u
  exact ⟨v, edge, fun w other =>
    graph.unique_route_cut_vertex_at_most_one_neighbor small_faces a T u unique w v other edge⟩

include graph small_faces in
/-- If the source shares a face with every original vertex, the leaves
are precisely the original nonsource vertices. -/
theorem cofacial_source_leaf_iff_original (a : frontier P.body) (T : P.CutLocusTree a)
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val)
    (u : T.vertices) : (∃! v, T.graph.Adj u v) ↔ (u : Space) ∈ P.vertices := by
  constructor
  · rintro ⟨v, edge, only_neighbor⟩
    exact graph.cut_graph_leaf_is_vertex small_faces a T.toEmbeddedCutGraph u v edge only_neighbor
  · intro original
    obtain ⟨F, source, target⟩ := cofacial ⟨u, original⟩
    exact graph.unique_route_cut_vertex_is_leaf small_faces a T u
      (P.geodesicFiber_cofacial_unique a (T.vertexTarget u) F source target)

include graph small_faces in
/-- An actual passage between distinct incident edges cannot be at an
original vertex for a cofacial source. -/
theorem cofacial_source_internal_vertex_nonvertex (a : frontier P.body) (T : P.CutLocusTree a)
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val)
    (u v w : T.vertices) (first : T.graph.Adj u v) (second : T.graph.Adj u w)
    (different : v ≠ w) : (u : Space) ∉ P.vertices := by
  intro original
  obtain ⟨F, source, target⟩ := cofacial ⟨u, original⟩
  exact different (graph.cofacial_cut_vertex_at_most_one_neighbor small_faces a T u
    F source target v w first second)

include graph small_faces in
/-- The real flat fan exists at every internal tree-path junction;
there is no remaining singular-junction premise in this cofacial case. -/
theorem cofacial_source_internal_junction_fan (a : frontier P.body) (T : P.CutLocusTree a)
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val)
    (u v w : T.vertices) (first : T.graph.Adj u v) (second : T.graph.Adj u w)
    (different : v ≠ w) : Nonempty (JunctionFan T u) :=
  graph.exists_junction_fan small_faces a T u
    (graph.cofacial_source_internal_vertex_nonvertex small_faces a T cofacial u v w first second different)

end SixVertexGraph
end SixVertexUnfolding.ConvexPolyhedron
