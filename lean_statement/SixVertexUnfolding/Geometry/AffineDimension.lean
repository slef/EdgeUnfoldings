import SixVertexUnfolding.Definitions

/-! Small affine-dimension lemmas in the fixed ambient space of the public statement. -/

namespace SixVertexUnfolding

theorem affineDimension_empty : affineDimension ∅ = 0 := by
  rw [affineDimension, AffineSubspace.span_empty, AffineSubspace.direction_bot]
  simp

theorem affineDimension_mono {s t : Set Space} (inclusion : s ⊆ t) :
    affineDimension s ≤ affineDimension t :=
  Submodule.finrank_mono (AffineSubspace.direction_le (affineSpan_mono ℝ inclusion))

theorem affineDimension_convexHull (s : Set Space) :
    affineDimension (convexHull ℝ s) = affineDimension s := by
  unfold affineDimension
  rw [affineSpan_convexHull]

theorem nonempty_of_affineDimension_pos {s : Set Space} (positive : 0 < affineDimension s) :
    s.Nonempty := by
  by_contra empty
  rw [Set.not_nonempty_iff_eq_empty.mp empty, affineDimension_empty] at positive
  omega

/-- A nonempty subset of equal affine dimension spans the same affine space. -/
theorem affineSpan_eq_of_subset_of_dimension_eq {s t : Set Space}
    (nonempty : s.Nonempty) (inclusion : s ⊆ t)
    (dimension_eq : affineDimension s = affineDimension t) :
    affineSpan ℝ s = affineSpan ℝ t := by
  have span_inclusion := affineSpan_mono ℝ inclusion
  have same_direction := Submodule.eq_of_le_of_finrank_eq
    (AffineSubspace.direction_le span_inclusion) dimension_eq
  exact AffineSubspace.eq_of_direction_eq_of_nonempty_of_le
    same_direction (nonempty.affineSpan ℝ) span_inclusion

theorem affineDimension_pair {a b : Space} (distinct : a ≠ b) :
    affineDimension {a, b} = 1 := by
  rw [affineDimension, direction_affineSpan, vectorSpan_pair]
  exact finrank_span_singleton (sub_ne_zero.mpr distinct)

theorem affineDimension_singleton (a : Space) : affineDimension {a} = 0 := by
  simp [affineDimension, direction_affineSpan]

end SixVertexUnfolding
