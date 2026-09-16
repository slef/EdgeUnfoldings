import SixVertexUnfolding.Geometry.FaceSegments

/-! Finite subdivision vertices for a collection of cofacial segments:
all endpoints and all intersections between distinct supporting lines. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

namespace FaceSegment

variable {P : ConvexPolyhedron} (s : P.FaceSegment)

noncomputable def supportingLine : AffineSubspace ℝ Space := affineSpan ℝ ({s.first, s.last} : Set Space)

theorem on_supportingLine : s.points ⊆ s.supportingLine :=
  s.supportingLine.convex.segment_subset (left_mem_affineSpan_pair ℝ _ _) (right_mem_affineSpan_pair ℝ _ _)

theorem distinct_line_intersection_finite (t : P.FaceSegment) (different : s.supportingLine ≠ t.supportingLine) :
    (s.points ∩ t.points).Finite := by
  apply Set.Subsingleton.finite
  intro x hx y hy
  by_contra xy
  have first := affineSpan_pair_eq_of_mem_of_mem_of_ne (s.on_supportingLine hx.1) (s.on_supportingLine hy.1) xy
  have second := affineSpan_pair_eq_of_mem_of_mem_of_ne (t.on_supportingLine hx.2) (t.on_supportingLine hy.2) xy
  exact different (first.symm.trans second)

end FaceSegment

def segmentCrossings {P : ConvexPolyhedron} (segments : Set P.FaceSegment) : Set Space :=
  {x | ∃ s ∈ segments, ∃ t ∈ segments, s.supportingLine ≠ t.supportingLine ∧ x ∈ s.points ∩ t.points}

def segmentVertices {P : ConvexPolyhedron} (segments : Set P.FaceSegment) : Set Space :=
  (FaceSegment.first '' segments ∪ FaceSegment.last '' segments) ∪ segmentCrossings segments

theorem segmentCrossings_finite {P : ConvexPolyhedron} (segments : Set P.FaceSegment) (finite : segments.Finite) :
    (segmentCrossings segments).Finite := by
  letI : Finite segments := finite
  let pieces (s t : segments) := {x ∈ s.val.points ∩ t.val.points | s.val.supportingLine ≠ t.val.supportingLine}
  have each (s t : segments) : (pieces s t).Finite := by
    by_cases different : s.val.supportingLine ≠ t.val.supportingLine
    · exact (s.val.distinct_line_intersection_finite t.val different).subset (fun _ h => h.1)
    · have empty : pieces s t = ∅ := by ext x; simp [pieces, different]
      rw [empty]
      exact finite_empty
  apply (finite_iUnion (fun s => finite_iUnion (each s))).subset
  rintro x ⟨s, hs, t, ht, different, member⟩
  exact mem_iUnion.mpr ⟨⟨s, hs⟩, mem_iUnion.mpr ⟨⟨t, ht⟩, member, different⟩⟩

theorem segmentVertices_finite {P : ConvexPolyhedron} (segments : Set P.FaceSegment) (finite : segments.Finite) :
    (segmentVertices segments).Finite :=
  ((finite.image _).union (finite.image _)).union (segmentCrossings_finite segments finite)

theorem segmentVertices_covered {P : ConvexPolyhedron} (segments : Set P.FaceSegment) :
    segmentVertices segments ⊆ ⋃ s ∈ segments, s.points := by
  intro x hx
  rcases hx with (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩) | ⟨s, hs, t, _, _, member⟩
  · exact mem_iUnion.mpr ⟨s, mem_iUnion.mpr ⟨hs, left_mem_segment ℝ _ _⟩⟩
  · exact mem_iUnion.mpr ⟨s, mem_iUnion.mpr ⟨hs, right_mem_segment ℝ _ _⟩⟩
  · exact mem_iUnion.mpr ⟨s, mem_iUnion.mpr ⟨hs, member.1⟩⟩

end SixVertexUnfolding.ConvexPolyhedron
