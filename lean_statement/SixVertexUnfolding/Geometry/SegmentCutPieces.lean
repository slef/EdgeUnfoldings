import SixVertexUnfolding.Geometry.FaceSegments
import SixVertexUnfolding.Geometry.SegmentCutIntervals

/-! Convert the checked parameter intervals into actual closed surface
segments. This includes the degenerate singleton case. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- The actual cut set meets a cofacial segment in exactly finitely many cofacial closed segments. -/
theorem segment_cut_finite_pieces (a : frontier P.body) (s : P.FaceSegment) :
    ∃ pieces : Set P.FaceSegment, pieces.Finite ∧
      ∀ x, x ∈ s.points ∩ P.cutSetInSpace a ↔ ∃ p ∈ pieces, x ∈ p.points := by
  classical
  by_cases same : s.first = s.last
  · have singleton : s.points = {s.first} := by simp [FaceSegment.points, same]
    by_cases cut : s.first ∈ P.cutSetInSpace a
    · refine ⟨{s}, finite_singleton s, ?_⟩
      intro x
      simp only [singleton, mem_inter_iff, mem_singleton_iff, exists_eq_left]
      constructor
      · exact fun h => h.1
      · intro h
        exact ⟨h, h ▸ cut⟩
    · refine ⟨∅, finite_empty, ?_⟩
      intro x
      simp only [singleton, mem_inter_iff, mem_singleton_iff, mem_empty_iff_false, false_and, exists_false, iff_false]
      rintro ⟨rfl, member⟩
      exact cut member
  · let curve : ℝ →ᵃ[ℝ] Space := AffineMap.lineMap s.first s.last
    have left : curve 0 ∈ s.face.val := by simpa only [curve, AffineMap.lineMap_apply_zero] using s.first_mem
    have right : curve 1 ∈ s.face.val := by simpa only [curve, AffineMap.lineMap_apply_one] using s.last_mem
    obtain ⟨intervals, finite_intervals, inside, exact_intervals⟩ := graph.segment_cut_finite_intervals
      small_faces a s.face curve (AffineMap.lineMap_injective ℝ same) (by norm_num : (0 : ℝ) < 1) left right
    let make (p : intervals) : P.FaceSegment := {
      face := s.face
      first := curve p.val.1
      last := curve p.val.2
      first_mem := affine_interval_in_face s.face curve (by norm_num : (0 : ℝ) ≤ 1) left right
        _ ((inside _ p.property).2 (left_mem_Icc.mpr (inside _ p.property).1)).1
      last_mem := affine_interval_in_face s.face curve (by norm_num : (0 : ℝ) ≤ 1) left right
        _ ((inside _ p.property).2 (right_mem_Icc.mpr (inside _ p.property).1)).1 }
    letI : Finite intervals := finite_intervals
    refine ⟨range make, finite_range make, ?_⟩
    have image_piece (p : intervals) : (make p).points = curve '' Icc p.val.1 p.val.2 := by
      rw [← segment_eq_Icc (inside _ p.property).1, image_segment]
      rfl
    have whole : s.points = curve '' Icc (0 : ℝ) 1 := by
      rw [← segment_eq_Icc (by norm_num : (0 : ℝ) ≤ 1), image_segment]
      simp only [curve, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one]
      rfl
    intro x
    constructor
    · rintro ⟨member, cut⟩
      rw [whole] at member
      obtain ⟨t, ht, rfl⟩ := member
      have parameter : t ∈ Icc (0 : ℝ) 1 ∩ curve ⁻¹' P.cutSetInSpace a := ⟨ht, cut⟩
      rw [exact_intervals] at parameter
      obtain ⟨p, member⟩ := mem_iUnion.mp parameter
      obtain ⟨hp, interval⟩ := mem_iUnion.mp member
      refine ⟨make ⟨p, hp⟩, mem_range_self _, ?_⟩
      rw [image_piece]
      exact ⟨t, interval, rfl⟩
    · rintro ⟨_, ⟨p, rfl⟩, member⟩
      rw [image_piece] at member
      obtain ⟨t, ht, rfl⟩ := member
      have parameter := (inside _ p.property).2 ht
      exact ⟨whole ▸ ⟨t, parameter.1, rfl⟩, parameter.2⟩

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
