import SixVertexUnfolding.Geometry.SmallPolyhedronUniqueRouteCutVertex
import SixVertexUnfolding.Geometry.UniqueRouteLeaves

/-! Original nonsource vertices are leaves for a cofacial source on a
small polyhedron. In particular, this applies to a universal vertex.
The conclusion supplies the original-leaf field of the star charts;
it does not assume that field as a geometric input. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

variable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include size small_faces in
/-- A cut-tree vertex reached by a unique shortest route has exactly one neighbor. -/
theorem small_unique_route_cut_vertex_is_leaf (a : frontier P.body) (T : P.CutLocusTree a)
    (u : T.vertices) (unique : (P.geodesicFiber a (T.vertexTarget u)).Subsingleton) :
    ∃! v, T.graph.Adj u v := by
  letI : Nontrivial T.vertices := T.toEmbeddedCutGraph.vertices_nontrivial
  obtain ⟨v, edge⟩ := T.tree.connected.preconnected.exists_adj_of_nontrivial u
  exact ⟨v, edge, fun w other =>
    small_unique_route_cut_vertex_at_most_one_neighbor size small_faces a T u unique w v other edge⟩

include size small_faces in
/-- Every original cut vertex is a leaf when the source shares a face with every vertex. -/
theorem small_cofacial_source_original_is_leaf (a : frontier P.body) (T : P.CutLocusTree a)
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val)
    (u : T.vertices) (original : (u : Space) ∈ P.vertices) :
    ∃! v, T.graph.Adj u v := by
  obtain ⟨F, source, target⟩ := cofacial ⟨u, original⟩
  exact small_unique_route_cut_vertex_is_leaf size small_faces a T u
    (P.geodesicFiber_cofacial_unique a (T.vertexTarget u) F source target)

include size small_faces in
/-- An internal passage between different tree edges avoids all original vertices. -/
theorem small_cofacial_source_internal_vertex_nonvertex
    (a : frontier P.body) (T : P.CutLocusTree a)
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val)
    (u v w : T.vertices) (first : T.graph.Adj u v) (second : T.graph.Adj u w)
    (different : v ≠ w) : (u : Space) ∉ P.vertices := by
  intro original
  obtain ⟨only, _, unique⟩ := small_cofacial_source_original_is_leaf size small_faces a T cofacial u original
  exact different ((unique v first).trans (unique w second).symm)

/-- A universal vertex shares an original face with every vertex, including itself. -/
theorem universal_source_cofacial (a : frontier P.body) (source : P.Vertex)
    (at_source : (a : Space) = (source : Space))
    (universal : ∀ v : P.Vertex, v ≠ source → P.edgeGraph.Adj source v) :
    ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val := by
  intro v
  by_cases same : v = source
  · obtain ⟨w, original, different⟩ := Finset.exists_mem_ne
      (show 1 < P.vertices.card by have := P.four_le_vertex_count; omega) (source : Space)
    have distinct : (⟨w, original⟩ : P.Vertex) ≠ source :=
      fun equal => different (congrArg Subtype.val equal)
    obtain ⟨_, F, G, _, edge⟩ := universal ⟨w, original⟩ distinct
    have inside : (source : Space) ∈ F.val ∩ G.val := by
      rw [edge]
      exact left_mem_segment ℝ _ _
    exact ⟨F, by simpa only [at_source] using inside.1, by simpa only [same] using inside.1⟩
  · obtain ⟨_, F, G, _, edge⟩ := universal v same
    have first : (source : Space) ∈ F.val ∩ G.val := by
      rw [edge]
      exact left_mem_segment ℝ _ _
    have last : (v : Space) ∈ F.val ∩ G.val := by
      rw [edge]
      exact right_mem_segment ℝ _ _
    exact ⟨F, by simpa only [at_source] using first.1, last.1⟩

include size small_faces in
/-- Universal sources supply the original-leaf condition required by the star construction. -/
theorem small_universal_source_original_is_leaf
    (a : frontier P.body) (source : P.Vertex) (at_source : (a : Space) = (source : Space))
    (universal : ∀ v : P.Vertex, v ≠ source → P.edgeGraph.Adj source v)
    (T : P.CutLocusTree a) (u : T.vertices) (original : (u : Space) ∈ P.vertices) :
    ∃! v, T.graph.Adj u v :=
  small_cofacial_source_original_is_leaf size small_faces a T
    (universal_source_cofacial a source at_source universal) u original

end SixVertexUnfolding.ConvexPolyhedron
