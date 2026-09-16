import SixVertexUnfolding.Geometry.FaceCutCover
import SixVertexUnfolding.Geometry.SegmentCutPieces

/-! Exact global finite-segment structure of the actual compact cut set.
The finite graph subdivision and tree conclusion are separate next steps. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- The cut set is exactly a finite union of closed segments in whole original facets. -/
theorem cutSet_finite_segments (a : frontier P.body) :
    ∃ segments : Set P.FaceSegment, segments.Finite ∧
      P.cutSetInSpace a = ⋃ s ∈ segments, s.points := by
  obtain ⟨cover, finite_cover, covers⟩ := graph.cut_finite_segment_cover small_faces a
  letI : Finite cover := finite_cover
  choose pieces finite_pieces exact_pieces using
    (fun s : cover => graph.segment_cut_finite_pieces small_faces a s.val)
  refine ⟨⋃ s : cover, pieces s, finite_iUnion finite_pieces, ?_⟩
  ext x
  constructor
  · intro cut
    obtain ⟨s, hs, on_segment⟩ := covers x cut
    obtain ⟨p, hp, on_piece⟩ := (exact_pieces ⟨s, hs⟩ x).mp ⟨on_segment, cut⟩
    exact mem_iUnion.mpr ⟨p, mem_iUnion.mpr ⟨mem_iUnion.mpr ⟨⟨s, hs⟩, hp⟩, on_piece⟩⟩
  · intro member
    obtain ⟨p, member⟩ := mem_iUnion.mp member
    obtain ⟨hp, on_piece⟩ := mem_iUnion.mp member
    obtain ⟨s, hp⟩ := mem_iUnion.mp hp
    exact ((exact_pieces s x).mpr ⟨p, hp, on_piece⟩).2

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
