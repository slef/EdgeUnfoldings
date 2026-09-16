import SixVertexUnfolding.Geometry.MarkedCutGraph
import SixVertexUnfolding.Geometry.CutTreeOriginalVertices

/-! An actual cut-locus tree, subdivided at every original vertex and
junction. Every open tree edge consequently has exactly two shortest routes. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- Junctions are genuine multiple-route targets, hence belong to the cut set. -/
theorem junctions_subset_cutSet (P : ConvexPolyhedron) (a : frontier P.body) :
    P.junctions a ⊆ P.cutSet a := by
  rintro b ⟨different, f, hf, g, hg, h, hh, fg, fh, gh⟩
  exact Or.inl ((P.multiple_routes_iff_fiber a b).mpr ⟨different, fun unique => fg (unique hf hg)⟩)

/-- Every point marked for subdivision already belongs to the actual cut set. -/
theorem cutExceptions_subset_cutSet (P : ConvexPolyhedron) (a : frontier P.body) :
    P.cutExceptions a ⊆ P.cutSet a := by
  rintro b (junction | vertex)
  · exact P.junctions_subset_cutSet a junction
  · exact Or.inr vertex

/-- The embedded cut tree with all exceptional cut points marked as graph vertices. -/
structure CutLocusTree (P : ConvexPolyhedron) (a : frontier P.body) extends P.EmbeddedCutGraph a where
  tree : graph.IsTree
  exceptional_vertices : ∀ b ∈ P.cutExceptions a, (b : Space) ∈ vertices

namespace CutLocusTree

variable {P : ConvexPolyhedron} {a : frontier P.body} (T : P.CutLocusTree a)

/-- No junction or original vertex lies inside an open edge of the refined cut tree. -/
theorem open_edge_regular {u v : T.vertices} (edge : T.graph.Adj u v)
    (b : frontier P.body) (inside : (b : Space) ∈ openSegment ℝ (u : Space) (v : Space)) :
    b ∉ P.cutExceptions a := by
  intro exceptional
  exact disjoint_left.mp (T.no_vertex_inside u v edge) inside (T.exceptional_vertices b exceptional)

/-- A point of an open tree edge belongs to the actual cut set. -/
theorem open_edge_cut {u v : T.vertices} (edge : T.graph.Adj u v)
    (b : frontier P.body) (inside : (b : Space) ∈ openSegment ℝ (u : Space) (v : Space)) :
    b ∈ P.cutSet a := by
  apply (P.mem_cutSetInSpace a b).mp
  exact (T.trace b).mpr (Or.inr ⟨u, v, edge, inside⟩)

end CutLocusTree

namespace SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- The finite cut tree can be subdivided so every open edge is a regular two-route interval. -/
theorem exists_regular_cut_tree (a : frontier P.body) : Nonempty (P.CutLocusTree a) := by
  let marks : Set Space := Subtype.val '' P.cutExceptions a
  have finite_marks : marks.Finite := (graph.cutExceptions_finite small_faces a).image Subtype.val
  have marks_cut : marks ⊆ P.cutSetInSpace a := by
    rintro _ ⟨b, exceptional, rfl⟩
    exact ⟨b, P.cutExceptions_subset_cutSet a exceptional, rfl⟩
  obtain ⟨K, contains⟩ := graph.exists_cut_graph_containing small_faces a marks finite_marks marks_cut
  exact ⟨{
    toEmbeddedCutGraph := K
    tree := graph.embedded_cut_graph_isTree small_faces a K
    exceptional_vertices := fun b exceptional => contains ⟨b, exceptional, rfl⟩ }⟩

include graph small_faces in
/-- Every point strictly inside an edge has exactly two actual normalized shortest routes. -/
theorem cut_tree_open_edge_two_routes (a : frontier P.body) (T : P.CutLocusTree a)
    {u v : T.vertices} (edge : T.graph.Adj u v) (b : frontier P.body)
    (inside : (b : Space) ∈ openSegment ℝ (u : Space) (v : Space)) :
    Nat.card (P.geodesicFiber a b) = 2 :=
  (graph.regular_cut_point small_faces a b (T.open_edge_cut edge b inside)
    (T.open_edge_regular edge b inside)).1

end SixVertexGraph
end SixVertexUnfolding.ConvexPolyhedron
