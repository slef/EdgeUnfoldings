import SixVertexUnfolding.Geometry.FiniteSourceImages
import SixVertexUnfolding.Geometry.VoronoiSeparation

/-! Equal-distance loci of distinct developed source copies form a finite
collection of explicit straight lines in each target facet's plane. -/

namespace SixVertexUnfolding

open Set

/-- The equal-distance locus is the perpendicular bisector, in explicit linear coordinates. -/
theorem equal_site_distances_iff_bisector (p q x : Plane) :
    dist p x = dist q x ↔ inner ℝ (q - p) x = (‖q‖ ^ 2 - ‖p‖ ^ 2) / 2 := by
  rw [dist_comm p x, dist_comm q x]
  have opposite : inner ℝ (p - q) x = -inner ℝ (q - p) x := by
    simp only [inner_sub_left]
    ring
  constructor
  · intro equal
    have left := (nearer_site_iff_halfplane x p q).mp equal.le
    have right := (nearer_site_iff_halfplane x q p).mp equal.ge
    rw [opposite] at right
    linarith
  · intro equal
    apply le_antisymm
    · exact (nearer_site_iff_halfplane x p q).mpr equal.le
    · apply (nearer_site_iff_halfplane x q p).mpr
      rw [opposite, equal]
      linarith

namespace ConvexPolyhedron

/-- Perpendicular bisectors of distinct source copies in one target face. -/
def sourceBisectors (P : ConvexPolyhedron) (a : Space) (F : P.Face) : Set (Set Plane) :=
  {line | ∃ p ∈ P.sourceImages a F, ∃ q ∈ P.sourceImages a F,
    p ≠ q ∧ line = {x | dist p x = dist q x}}

theorem sourceBisectors_finite (P : ConvexPolyhedron) (a : Space) (F : P.Face) :
    (P.sourceBisectors a F).Finite := by
  have pairs := (P.sourceImages_finite a F).prod (P.sourceImages_finite a F)
  have images := pairs.image (fun pair : Plane × Plane => {x | dist pair.1 x = dist pair.2 x})
  apply images.subset
  rintro line ⟨p, hp, q, hq, _, rfl⟩
  exact ⟨(p, q), ⟨hp, hq⟩, rfl⟩

/-- Every candidate line has a nonzero normal and an explicit affine equation. -/
theorem sourceBisector_equation (P : ConvexPolyhedron) (a : Space) (F : P.Face)
    (line : Set Plane) (member : line ∈ P.sourceBisectors a F) :
    ∃ normal : Plane, normal ≠ 0 ∧ ∃ c : ℝ, line = {x | inner ℝ normal x = c} := by
  obtain ⟨p, _, q, _, different, rfl⟩ := member
  refine ⟨q - p, sub_ne_zero.mpr different.symm, (‖q‖ ^ 2 - ‖p‖ ^ 2) / 2, ?_⟩
  ext x
  exact equal_site_distances_iff_bisector p q x

theorem sourceBisector_closed (P : ConvexPolyhedron) (a : Space) (F : P.Face)
    (line : Set Plane) (member : line ∈ P.sourceBisectors a F) : IsClosed line := by
  obtain ⟨p, _, q, _, _, rfl⟩ := member
  exact isClosed_eq (continuous_const.dist continuous_id) (continuous_const.dist continuous_id)

/-- All source-copy tie loci together form a closed finite union of lines. -/
theorem sourceBisectors_union_closed (P : ConvexPolyhedron) (a : Space) (F : P.Face) :
    IsClosed (⋃₀ P.sourceBisectors a F) := by
  letI : Fintype (P.sourceBisectors a F) := (P.sourceBisectors_finite a F).fintype
  have closed : IsClosed (⋃ line : P.sourceBisectors a F, (line : Set Plane)) :=
    isClosed_iUnion_of_finite (fun line => P.sourceBisector_closed a F line line.property)
  convert closed using 1
  ext x
  simp only [mem_sUnion, mem_iUnion, Subtype.exists, exists_prop]

end ConvexPolyhedron
end SixVertexUnfolding
