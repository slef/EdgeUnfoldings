import SixVertexUnfolding.Geometry.EdgeGraph
import SixVertexUnfolding.Geometry.EdgeIncidence

/-! The two original facets incident to a specified original vertex-edge pair. -/

namespace SixVertexUnfolding.ConvexPolyhedron

/-- Every original edge has two distinct incident facets, and there are no others. -/
theorem edge_incident_faces (P : ConvexPolyhedron) (a b : P.Vertex) (edge : P.edgeGraph.Adj a b) :
    ∃ F G : P.Face, F ≠ G ∧
      (a : Space) ∈ F.val ∧ (b : Space) ∈ F.val ∧
      (a : Space) ∈ G.val ∧ (b : Space) ∈ G.val ∧
      ∀ H : P.Face, (a : Space) ∈ H.val → (b : Space) ∈ H.val → H = F ∨ H = G := by
  obtain ⟨_, F, G, shared, edge_eq⟩ := edge
  have at_a : (a : Space) ∈ F.val ∩ G.val := by
    rw [edge_eq]
    exact left_mem_segment ℝ (a : Space) (b : Space)
  have at_b : (b : Space) ∈ F.val ∩ G.val := by
    rw [edge_eq]
    exact right_mem_segment ℝ (a : Space) (b : Space)
  refine ⟨F, G, ?_, at_a.1, at_b.1, at_a.2, at_b.2, ?_⟩
  · intro same
    subst G
    exact F.shareEdge_irrefl shared
  · intro H aH bH
    apply F.facets_containing_shared_edge G shared H
    rw [edge_eq]
    exact H.convex.segment_subset aH bH

end SixVertexUnfolding.ConvexPolyhedron
