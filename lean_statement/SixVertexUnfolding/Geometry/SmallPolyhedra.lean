import SixVertexUnfolding.Geometry.VertexFigureEdges
import SixVertexUnfolding.SmallGraphs

/-! The first graph classification results, now for the public geometric polyhedron. -/

namespace SixVertexUnfolding.ConvexPolyhedron

variable (P : ConvexPolyhedron)

@[simp] theorem vertex_card : Fintype.card P.Vertex = P.vertices.card := by simp [Vertex]

/-- With four vertices, every pair of different original vertices is joined by an original edge. -/
theorem four_vertices_all_adjacent (size : P.vertices.card = 4) (v w : P.Vertex)
    (distinct : w ≠ v) : P.edgeGraph.Adj v w := by
  classical
  letI : P.edgeGraph.LocallyFinite := P.edgeGraph.neighborSetFintype
  apply SmallGraphs.adjacent_to_all_of_max_degree P.edgeGraph v _ w distinct
  have lower : 3 ≤ P.edgeGraph.degree v := by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using P.edgeGraph_min_degree v
  have upper := P.edgeGraph.degree_lt_card_verts v
  rw [P.vertex_card] at upper ⊢
  omega

/-- Every four- or five-vertex convex polyhedron has a vertex joined to every other vertex. -/
theorem at_most_five_has_universal_vertex (size : P.vertices.card ≤ 5) :
    ∃ v : P.Vertex, ∀ w, w ≠ v → P.edgeGraph.Adj v w := by
  classical
  letI : P.edgeGraph.LocallyFinite := P.edgeGraph.neighborSetFintype
  have lower := P.four_le_vertex_count
  have minimum_degree (v : P.Vertex) : 3 ≤ P.edgeGraph.degree v := by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using P.edgeGraph_min_degree v
  have cases : P.vertices.card = 4 ∨ P.vertices.card = 5 := by omega
  rcases cases with four | five
  · apply SmallGraphs.four_vertices_have_universal_vertex P.edgeGraph
      (by simpa using four) minimum_degree
  · apply SmallGraphs.five_vertices_have_universal_vertex P.edgeGraph
      (by simpa using five) minimum_degree

/-- In the remaining six-vertex case, each vertex has one or two nonneighbors. -/
theorem six_vertices_complement_degrees (size : P.vertices.card = 6)
    (no_universal : ¬ ∃ v : P.Vertex, ∀ w, w ≠ v → P.edgeGraph.Adj v w) (v : P.Vertex) :
    P.edgeGraphᶜ.degree v = 1 ∨ P.edgeGraphᶜ.degree v = 2 := by
  classical
  letI : P.edgeGraph.LocallyFinite := P.edgeGraph.neighborSetFintype
  have minimum_degree (w : P.Vertex) : 3 ≤ P.edgeGraph.degree w := by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using P.edgeGraph_min_degree w
  have no_five (w : P.Vertex) : P.edgeGraph.degree w ≠ 5 := by
    intro degree_five
    apply no_universal
    exact ⟨w, SmallGraphs.adjacent_to_all_of_max_degree P.edgeGraph w
      (by simpa [size] using degree_five)⟩
  simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using
    SmallGraphs.six_vertex_complement_degrees P.edgeGraph (by simpa using size)
      minimum_degree no_five v

end SixVertexUnfolding.ConvexPolyhedron
