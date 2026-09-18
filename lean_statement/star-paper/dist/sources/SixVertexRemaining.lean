import SixVertexUnfolding.Reduction
import SixVertexUnfolding.MinusEdge
import SixVertexUnfolding.PrismComplete

/-! The remaining six-vertex work is confined to universal vertices and the prism with a diagonal. -/

namespace SixVertexUnfolding

/-- The concrete graph labels already certify the exact number of original vertices. -/
theorem ConvexPolyhedron.SixVertexGraph.vertex_count {P : ConvexPolyhedron} (graph : P.SixVertexGraph) :
    P.vertices.card = 6 := by
  have count := Fintype.card_congr graph.vertex
  simpa only [P.vertex_card, Fintype.card_fin] using count.symm

/-- The complete octahedron case needs no separate assumption on facet sizes. -/
theorem every_convex_octahedron (P : ConvexPolyhedron) (graph : P.SixVertexGraph)
    (octahedral : graph.kind = .octahedron) : P.HasEdgeUnfolding := by
  rcases six_vertex_reduction P graph.vertex_count with unfolded | small_faces
  · exact unfolded
  · exact graph.hasEdgeUnfolding_of_octahedron small_faces octahedral

/-- The complete single-quadrilateral case also needs no separate facet-size assumption. -/
theorem every_convex_octahedron_minus_edge (P : ConvexPolyhedron) (graph : P.SixVertexGraph)
    (kind : graph.kind = .minusEdge) : P.HasEdgeUnfolding := by
  rcases six_vertex_reduction P graph.vertex_count with unfolded | small_faces
  · exact unfolded
  · exact graph.hasEdgeUnfolding_of_minusEdge small_faces kind

/-- The complete ordinary-prism case needs no separate assumption on facet sizes or parallelism. -/
theorem every_convex_triangular_prism (P : ConvexPolyhedron) (graph : P.SixVertexGraph)
    (kind : graph.kind = .prism) : P.HasEdgeUnfolding := by
  rcases six_vertex_reduction P graph.vertex_count with unfolded | small_faces
  · exact unfolded
  · exact graph.hasEdgeUnfolding_of_prism small_faces kind

/-- The completed constructions eliminate the octahedron and its single-quadrilateral variant. -/
theorem unfolding_or_universal_or_prism (P : ConvexPolyhedron) (at_most_six : P.vertices.card ≤ 6) :
    P.HasEdgeUnfolding ∨
      (P.vertices.card = 6 ∧
        (∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
          (F.val ∩ (P.vertices : Set Space)).ncard = 4) ∧
        ((∃ v : P.Vertex, ∀ w, w ≠ v → P.edgeGraph.Adj v w) ∨
          ∃ graph : P.SixVertexGraph, graph.kind = .prismDiagonal ∨ graph.kind = .prism)) := by
  rcases unfolding_or_remaining_cases P at_most_six with unfolded | ⟨size, small_faces⟩
  · exact Or.inl unfolded
  by_cases universal : ∃ v : P.Vertex, ∀ w, w ≠ v → P.edgeGraph.Adj v w
  · exact Or.inr ⟨size, small_faces, Or.inl universal⟩
  obtain ⟨graph⟩ := P.exists_six_vertex_graph size universal small_faces
  cases kind : graph.kind with
  | octahedron => exact Or.inl (graph.hasEdgeUnfolding_of_octahedron small_faces kind)
  | minusEdge => exact Or.inl (graph.hasEdgeUnfolding_of_minusEdge small_faces kind)
  | prismDiagonal => exact Or.inr ⟨size, small_faces, Or.inr ⟨graph, Or.inl kind⟩⟩
  | prism => exact Or.inr ⟨size, small_faces, Or.inr ⟨graph, Or.inr kind⟩⟩

/-- Every input is now settled except the universal-vertex case and the prism-with-diagonal case. -/
theorem unfolding_or_universal_or_prismDiagonal (P : ConvexPolyhedron) (at_most_six : P.vertices.card ≤ 6) :
    P.HasEdgeUnfolding ∨
      (P.vertices.card = 6 ∧
        (∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
          (F.val ∩ (P.vertices : Set Space)).ncard = 4) ∧
        ((∃ v : P.Vertex, ∀ w, w ≠ v → P.edgeGraph.Adj v w) ∨
          ∃ graph : P.SixVertexGraph, graph.kind = .prismDiagonal)) := by
  rcases unfolding_or_universal_or_prism P at_most_six with unfolded | ⟨size, small_faces, cases⟩
  · exact Or.inl unfolded
  rcases cases with universal | ⟨graph, kind | kind⟩
  · exact Or.inr ⟨size, small_faces, Or.inl universal⟩
  · exact Or.inr ⟨size, small_faces, Or.inr ⟨graph, kind⟩⟩
  · exact Or.inl (graph.hasEdgeUnfolding_of_prism small_faces kind)

end SixVertexUnfolding
