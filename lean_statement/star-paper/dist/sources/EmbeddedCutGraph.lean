import SixVertexUnfolding.Geometry.FiniteCutSegments
import SixVertexUnfolding.Geometry.SegmentGraphEmbedding

/-! A finite graph embedded in the actual polyhedral boundary, whose
vertices and straight edges form exactly the compact cut set. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- The finite embedded graph data. Connectivity and acyclicity are deliberately separate conclusions. -/
structure EmbeddedCutGraph (P : ConvexPolyhedron) (a : frontier P.body) where
  vertices : Set Space
  finite_vertices : vertices.Finite
  graph : SimpleGraph vertices
  trace : ∀ x, x ∈ P.cutSetInSpace a ↔ x ∈ vertices ∨
    ∃ u v : vertices, graph.Adj u v ∧ x ∈ openSegment ℝ (u : Space) (v : Space)
  cofacial_edges : ∀ u v : vertices, graph.Adj u v →
    ∃ F : P.Face, segment ℝ (u : Space) (v : Space) ⊆ F.val
  no_vertex_inside : ∀ u v : vertices, graph.Adj u v →
    Disjoint (openSegment ℝ (u : Space) (v : Space)) vertices
  open_edges_meet : ∀ u v w z : vertices, graph.Adj u v → graph.Adj w z →
    ∀ x ∈ openSegment ℝ (u : Space) (v : Space), x ∈ openSegment ℝ (w : Space) (z : Space) →
      (u = w ∧ v = z) ∨ (u = z ∧ v = w)

namespace SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- The actual cut set of every canonical model is a finite embedded graph of cofacial straight edges. -/
theorem exists_embedded_cut_graph (a : frontier P.body) : Nonempty (P.EmbeddedCutGraph a) := by
  obtain ⟨segments, finite, exact_segments⟩ := graph.cutSet_finite_segments small_faces a
  refine ⟨{
    vertices := segmentVertices segments
    finite_vertices := segmentVertices_finite segments finite
    graph := segmentGraph segments
    trace := ?_
    cofacial_edges := ?_
    no_vertex_inside := fun _ _ edge => edge.2.2
    open_edges_meet := fun _ _ _ _ first second _ hx hy =>
      segmentGraph_open_edges_meet segments first second hx hy }⟩
  · intro x
    rw [exact_segments]
    exact segmentGraph_trace segments finite x
  · intro u v edge
    obtain ⟨s, _, hu, hv⟩ := edge.2.1
    exact ⟨s.face, (s.convex.segment_subset hu hv).trans s.in_face⟩

end SixVertexGraph
end SixVertexUnfolding.ConvexPolyhedron
