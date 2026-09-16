import SixVertexUnfolding.Geometry.RetainedFaceGraph
import SixVertexUnfolding.Geometry.QuadrilateralSplit

/-! Supporting faces control where straight star cuts can meet them.
If any point of an original edge survives, its entire open edge survives. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- A nonvertex cut point on a face forces the source itself onto that face. -/
theorem starCut_face_contains_source {P : ConvexPolyhedron} (a b : frontier P.body) (F : P.Face)
    (member : (b : Space) ∈ F.val) (nonvertex : (b : Space) ∉ P.vertices)
    (on_cut : b ∈ P.starCuts a) : (a : Space) ∈ F.val := by
  obtain ⟨v, between⟩ := on_cut
  by_cases same : (a : Space) = (b : Space)
  · exact same.symm ▸ member
  have target_different : (v : Space) ≠ (b : Space) := fun equal => nonvertex (equal ▸ v.property)
  exact F.isExposed.isExtreme.left_mem_of_mem_openSegment
    (P.body_closed.frontier_subset a.property) (P.vertices_subset_body v.property) member
    (mem_openSegment_of_ne_left_right same target_different between)

/-- If the source is on an original edge, that whole edge is removed by the star cuts. -/
theorem shared_edge_cut_of_source_mem {P : ConvexPolyhedron} (a : frontier P.body)
    (F G : P.Face) (shared : P.ShareEdge F G) (source : (a : Space) ∈ F.val ∩ G.val) :
    ∀ b : frontier P.body, (b : Space) ∈ F.val ∩ G.val → b ∈ P.starCuts a := by
  obtain ⟨u, u_original, v, v_original, _, edge⟩ := F.shared_edge_endpoints G shared
  rw [edge] at source
  intro b member
  rw [edge, segment_split_at u v (a : Space) source] at member
  rcases member with first | last
  · exact ⟨⟨u, u_original⟩, by rwa [segment_symm]⟩
  · exact ⟨⟨v, v_original⟩, last⟩

/-- A retained adjacency preserves every nonvertex point of its original shared edge. -/
theorem retained_edge_nonvertex_uncut {P : ConvexPolyhedron} {a : frontier P.body}
    (F G : P.Face) (adjacent : (P.retainedFaceGraph a).Adj F G)
    (b : frontier P.body) (common : (b : Space) ∈ F.val ∩ G.val)
    (nonvertex : (b : Space) ∉ P.vertices) : b ∉ P.starCuts a := by
  intro on_cut
  have source : (a : Space) ∈ F.val ∩ G.val :=
    ⟨starCut_face_contains_source a b F common.1 nonvertex on_cut,
      starCut_face_contains_source a b G common.2 nonvertex on_cut⟩
  have shared := P.retainedFaceGraph_original a adjacent
  obtain ⟨_, c, c_common⟩ := adjacent
  exact c.property (shared_edge_cut_of_source_mem a F G shared source c.val c_common)

end SixVertexUnfolding.ConvexPolyhedron
