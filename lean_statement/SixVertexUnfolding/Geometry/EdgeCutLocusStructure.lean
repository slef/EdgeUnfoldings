import SixVertexUnfolding.Geometry.EdgeLocalVoronoi
import SixVertexUnfolding.Geometry.VoronoiJunctions

/-! The face-interior structure now extends across original edges: exactly
two routes give a bisector, and only finitely many junctions occur in each patch. -/

namespace SixVertexUnfolding.ConvexPolyhedron.EdgeFolding.MetricPatch

open Set

variable {P : ConvexPolyhedron} {center z : Space} {facets : P.NormalizedFacets center}
  {F G : P.Face} {chart : EdgeFolding facets F G} (patch : chart.MetricPatch z)
  (graph : P.SixVertexGraph)
  (small_faces : ∀ H : P.Face, (H.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (H.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- Exactly two routes give a full local bisector in the joined edge coordinates. -/
theorem two_route_local_bisector (a b : frontier P.body) (different : a ≠ b) (target : (b : Space) ∈ patch.domain)
    (two : Nat.card (P.geodesicFiber a b) = 2) :
    ∃ p ∈ chart.activeSources a b, ∃ q ∈ chart.activeSources a b, p ≠ q ∧
      ∃ V : Set Space, IsOpen V ∧ (b : Space) ∈ V ∧ V ⊆ patch.domain ∧ ∀ x ∈ V ∩ frontier P.body,
        (x ∈ P.multipleRouteLocus a ↔ dist p (chart.unfold x) = dist q (chart.unfold x)) := by
  have cardinal := (patch.activeSources_ncard graph small_faces a b different target).trans two
  obtain ⟨p, q, distinct, pair⟩ := ncard_eq_two.mp cardinal
  obtain ⟨V, openV, bV, contained, diagram⟩ := patch.local_voronoi_cut_locus graph small_faces a b different target
  refine ⟨p, by rw [pair]; simp, q, by rw [pair]; simp, distinct, V, openV, bV, contained, ?_⟩
  intro x hx
  rw [diagram x hx, pair, voronoiBoundary_pair p q distinct]
  rfl

include graph small_faces in
/-- Only finitely many targets in the whole edge patch have three or more shortest routes. -/
theorem junctions_finite (a : frontier P.body) :
    {b : frontier P.body | a ≠ b ∧ (b : Space) ∈ patch.domain ∧ 2 < Nat.card (P.geodesicFiber a b)}.Finite := by
  let junctions : Set (frontier P.body) := {b | a ≠ b ∧ (b : Space) ∈ patch.domain ∧ 2 < Nat.card (P.geodesicFiber a b)}
  have image_finite : ((fun b : frontier P.body => chart.unfold b) '' junctions).Finite := by
    apply (finite_three_site_centers (chart.sourceImages a) (chart.sourceImages_finite a)).subset
    rintro _ ⟨b, hb, rfl⟩
    have count : 2 < (chart.activeSources a b).ncard := by
      rw [patch.activeSources_ncard graph small_faces a b hb.1 hb.2.1]
      exact hb.2.2
    obtain ⟨p, hp, q, hq, r, hr, pq, pr, qr⟩ :=
      (two_lt_ncard (patch.activeSources_finite graph small_faces a b hb.1 hb.2.1)).mp count
    have subset := patch.activeSources_subset graph small_faces a b hb.1 hb.2.1
    have pvalue := chart.activeSource_distance patch a b hb.2.1 p hp
    exact ⟨p, subset hp, q, subset hq, r, subset hr, pq, pr, qr,
      pvalue.symm.trans (chart.activeSource_distance patch a b hb.2.1 q hq),
      pvalue.symm.trans (chart.activeSource_distance patch a b hb.2.1 r hr)⟩
  apply image_finite.of_finite_image
  intro b hb c hc same
  apply Subtype.ext
  change chart.unfold b = chart.unfold c at same
  have equal := congrArg chart.fold.map same
  rwa [chart.fold_unfold (patch.on_facets ⟨hb.2.1, b.property⟩), chart.fold_unfold (patch.on_facets ⟨hc.2.1, c.property⟩)] at equal

end SixVertexUnfolding.ConvexPolyhedron.EdgeFolding.MetricPatch
