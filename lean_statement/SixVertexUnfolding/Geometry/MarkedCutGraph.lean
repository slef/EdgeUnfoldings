import SixVertexUnfolding.Geometry.EmbeddedCutGraph

/-! Subdividing an exact finite segment graph at any prescribed finite
set of cut points preserves its geometric trace and all embedding properties. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

namespace EmbeddedCutGraph

/-- Assemble embedded graph data from any exact finite segment representation. -/
noncomputable def of_segments {P : ConvexPolyhedron} (a : frontier P.body)
    (segments : Set P.FaceSegment) (finite : segments.Finite)
    (exact_segments : P.cutSetInSpace a = ⋃ s ∈ segments, s.points) : P.EmbeddedCutGraph a where
  vertices := segmentVertices segments
  finite_vertices := segmentVertices_finite segments finite
  graph := segmentGraph segments
  trace := by
    intro x
    rw [exact_segments]
    exact segmentGraph_trace segments finite x
  cofacial_edges := by
    intro u v edge
    obtain ⟨s, _, hu, hv⟩ := edge.2.1
    exact ⟨s.face, (s.convex.segment_subset hu hv).trans s.in_face⟩
  no_vertex_inside := fun _ _ edge => edge.2.2
  open_edges_meet := fun _ _ _ _ first second _ hx hy =>
    segmentGraph_open_edges_meet segments first second hx hy

end EmbeddedCutGraph

namespace SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- Any finite set of actual cut points can be included among the graph's subdivision vertices. -/
theorem exists_cut_graph_containing (a : frontier P.body) (marks : Set Space)
    (finite_marks : marks.Finite) (marks_cut : marks ⊆ P.cutSetInSpace a) :
    ∃ K : P.EmbeddedCutGraph a, marks ⊆ K.vertices := by
  classical
  obtain ⟨segments, finite, exact_segments⟩ := graph.cutSet_finite_segments small_faces a
  letI : Finite marks := finite_marks
  have in_face (x : marks) : ∃ F : P.Face, (x : Space) ∈ F.val :=
    P.boundary_point_in_face (P.cutSetInSpace_subset_boundary a (marks_cut x.property))
  choose face member using in_face
  let point (x : marks) : P.FaceSegment := ⟨face x, x, x, member x, member x⟩
  let all := segments ∪ range point
  have finite_all : all.Finite := finite.union (finite_range point)
  have exact_all : P.cutSetInSpace a = ⋃ s ∈ all, s.points := by
    ext x
    constructor
    · intro cut
      rw [exact_segments] at cut
      obtain ⟨s, covered⟩ := mem_iUnion.mp cut
      obtain ⟨hs, member⟩ := mem_iUnion.mp covered
      exact mem_iUnion.mpr ⟨s, mem_iUnion.mpr ⟨Or.inl hs, member⟩⟩
    · intro covered
      obtain ⟨s, hs⟩ := mem_iUnion.mp covered
      obtain ⟨hs, member⟩ := mem_iUnion.mp hs
      rcases hs with old | ⟨y, rfl⟩
      · rw [exact_segments]
        exact mem_iUnion.mpr ⟨s, mem_iUnion.mpr ⟨old, member⟩⟩
      · have same : x = (y : Space) := by simpa only [point, FaceSegment.points, segment_same, mem_singleton_iff] using member
        exact same.symm ▸ marks_cut y.property
  refine ⟨EmbeddedCutGraph.of_segments a all finite_all exact_all, ?_⟩
  intro x hx
  exact Or.inl (Or.inl ⟨point ⟨x, hx⟩, Or.inr ⟨⟨x, hx⟩, rfl⟩, rfl⟩)

end SixVertexGraph
end SixVertexUnfolding.ConvexPolyhedron
