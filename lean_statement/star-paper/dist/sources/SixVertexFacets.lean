import SixVertexUnfolding.Geometry.SixVertexGraphs
import SixVertexUnfolding.Geometry.QuadrilateralLabels
import SixVertexUnfolding.Geometry.LabeledFacetIncidence
import SixVertexUnfolding.CanonicalFacetIncidence

/-! Identify every original whole facet in each of the four six-vertex graph forms. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)

/-- Each original triangle or quadrilateral is one of the graph's finite polygon candidates. -/
theorem facet_is_candidate (F : P.Face)
    (small : (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4) :
    F.vertexLabels graph.vertex ∈ graph.kind.candidates := by
  apply (SmallGraphs.SixGraphKind.isPolygon_iff_candidate _ _).mp
  rcases small with triangle | quadrilateral
  · refine Or.inl ⟨?_, ?_⟩
    · rw [F.vertexLabels_card]
      exact triangle
    · intro a aF b bF different
      exact (graph.edges a b).mp (F.adjacent_of_triangle triangle (graph.vertex a) (graph.vertex b)
        (graph.vertex.injective.ne different) ((F.mem_vertexLabels _ a).mp aF) ((F.mem_vertexLabels _ b).mp bF))
  · refine Or.inr ⟨?_, ?_⟩
    · rw [F.vertexLabels_card]
      exact quadrilateral
    · intro a aF
      have count := F.quadrilateral_label_neighbors graph.vertex quadrilateral a aF
      simpa only [graph.edges, SmallGraphs.SixGraphKind.adjacent] using count

/-- The finite list gives exactly the original whole facets of the geometric polyhedron. -/
theorem labeledFacets_eq
    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4) :
    labeledFacets graph.vertex = graph.kind.facets := by
  apply graph.kind.facets_determined
  · intro vertices member
    obtain ⟨F, rfl⟩ := (mem_labeledFacets graph.vertex vertices).mp member
    exact graph.facet_is_candidate F (small_faces F)
  · intro i j adjacent
    exact labeledFacets_edge_count graph.vertex i j ((graph.edges i j).mpr adjacent)
  · intro i j different nonedge
    exact labeledFacets_nonedge_count graph.vertex i j different (fun adjacent => nonedge ((graph.edges i j).mp adjacent))

/-- Existence of an original whole facet is equivalent to membership in the explicit facet list. -/
theorem exists_facet_iff
    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4) (vertices : Finset (Fin 6)) :
    (∃ F : P.Face, F.vertexLabels graph.vertex = vertices) ↔ vertices ∈ graph.kind.facets := by
  rw [← mem_labeledFacets, graph.labeledFacets_eq small_faces]

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
