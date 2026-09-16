import SixVertexUnfolding.Geometry.SourceBisectors

/-! The nearest-site ties of a finite set of planar sources. A ridge is the
part of one bisector on which neither defining site is beaten by another. -/

namespace SixVertexUnfolding

open Set

/-- The part of a bisector where the two sites are nearest. -/
def voronoiRidge (sources : Set Plane) (p q : Plane) : Set Plane :=
  {x | dist p x = dist q x ∧ ∀ r ∈ sources, dist p x ≤ dist r x}

/-- Points with at least two distinct nearest sites. -/
def voronoiBoundary (sources : Set Plane) : Set Plane :=
  {x | ∃ p ∈ sources, ∃ q ∈ sources, p ≠ q ∧ x ∈ voronoiRidge sources p q}

/-- Given an attained minimum value, a Voronoi tie means that its attaining site is not unique. -/
theorem mem_voronoiBoundary_iff_multiple_minima (sources : Set Plane) (x : Plane) (value : ℝ)
    (lower : ∀ p ∈ sources, value ≤ dist p x) (attained : ∃ p ∈ sources, value = dist p x) :
    x ∈ voronoiBoundary sources ↔ ¬ {p ∈ sources | dist p x = value}.Subsingleton := by
  constructor
  · rintro ⟨p, hp, q, hq, different, tie, nearest⟩ unique
    obtain ⟨r, hr, equal⟩ := attained
    have pvalue : dist p x = value := le_antisymm (equal ▸ nearest r hr) (lower p hp)
    exact different (unique ⟨hp, pvalue⟩ ⟨hq, tie.symm.trans pvalue⟩)
  · intro multiple
    obtain ⟨p, hp, q, hq, different⟩ := not_subsingleton_iff.mp multiple
    exact ⟨p, hp.1, q, hq.1, different, hp.2.trans hq.2.symm,
      fun r hr => hp.2 ▸ lower r hr⟩

/-- Each ridge is closed, even without finiteness of the site set. -/
theorem voronoiRidge_closed (sources : Set Plane) (p q : Plane) : IsClosed (voronoiRidge sources p q) := by
  have nearest : IsClosed (⋂ r : sources, {x : Plane | dist p x ≤ dist r.val x}) :=
    isClosed_iInter (fun r => isClosed_le (continuous_const.dist continuous_id) (continuous_const.dist continuous_id))
  have tied : IsClosed {x : Plane | dist p x = dist q x} :=
    isClosed_eq (continuous_const.dist continuous_id) (continuous_const.dist continuous_id)
  convert tied.inter nearest using 1
  ext x
  simp only [voronoiRidge, mem_inter_iff, mem_setOf_eq, mem_iInter, Subtype.forall]

/-- Distinct-site ridges lie on explicit straight lines with nonzero normals. -/
theorem voronoiRidge_on_line (sources : Set Plane) (p q : Plane) (different : p ≠ q) :
    q - p ≠ 0 ∧ voronoiRidge sources p q ⊆
      {x | inner ℝ (q - p) x = (‖q‖ ^ 2 - ‖p‖ ^ 2) / 2} :=
  ⟨sub_ne_zero.mpr different.symm, fun _ hx => (equal_site_distances_iff_bisector p q _).mp hx.1⟩

/-- Every ridge is convex: it is a bisector intersected with nearest-site halfplanes. -/
theorem voronoiRidge_convex (sources : Set Plane) (p q : Plane) : Convex ℝ (voronoiRidge sources p q) := by
  have tied : Convex ℝ {x : Plane | dist p x = dist q x} := by
    convert (convex_singleton ((‖q‖ ^ 2 - ‖p‖ ^ 2) / 2)).linear_preimage
      (innerSL ℝ (q - p)).toLinearMap using 1
    ext x
    exact equal_site_distances_iff_bisector p q x
  have halfplane (r : Plane) : Convex ℝ {x : Plane | dist p x ≤ dist r x} := by
    convert (convex_Iic ((‖r‖ ^ 2 - ‖p‖ ^ 2) / 2)).linear_preimage
      (innerSL ℝ (r - p)).toLinearMap using 1
    ext x
    simpa only [dist_comm] using nearer_site_iff_halfplane x p r
  have nearest := convex_iInter (fun r : sources => halfplane r.val)
  convert tied.inter nearest using 1
  ext x
  simp only [voronoiRidge, mem_inter_iff, mem_setOf_eq, mem_iInter, Subtype.forall]

/-- Finitely many sites give a finite union of closed convex pieces of explicit lines. -/
theorem voronoiBoundary_finite_pieces (sources : Set Plane) (finite : sources.Finite) :
    ∃ pieces : Set (Set Plane), pieces.Finite ∧ voronoiBoundary sources = ⋃₀ pieces ∧
      ∀ piece ∈ pieces, IsClosed piece ∧ Convex ℝ piece ∧
        ∃ normal : Plane, normal ≠ 0 ∧ ∃ level : ℝ, piece ⊆ {x | inner ℝ normal x = level} := by
  let pairs : Set (Plane × Plane) := {pair ∈ sources ×ˢ sources | pair.1 ≠ pair.2}
  let pieces := (fun pair : Plane × Plane => voronoiRidge sources pair.1 pair.2) '' pairs
  have finite_pairs : pairs.Finite := (finite.prod finite).subset (fun _ h => h.1)
  refine ⟨pieces, finite_pairs.image _, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨p, hp, q, hq, different, member⟩
      exact mem_sUnion.mpr ⟨voronoiRidge sources p q, ⟨(p, q), ⟨⟨hp, hq⟩, different⟩, rfl⟩, member⟩
    · rintro ⟨piece, ⟨⟨p, q⟩, ⟨⟨hp, hq⟩, different⟩, rfl⟩, member⟩
      exact ⟨p, hp, q, hq, different, member⟩
  · rintro piece ⟨⟨p, q⟩, ⟨_, different⟩, rfl⟩
    have line := voronoiRidge_on_line sources p q different
    exact ⟨voronoiRidge_closed sources p q, voronoiRidge_convex sources p q,
      q - p, line.1, (‖q‖ ^ 2 - ‖p‖ ^ 2) / 2, line.2⟩

end SixVertexUnfolding
