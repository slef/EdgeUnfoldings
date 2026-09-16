import SixVertexUnfolding.Geometry.EdgeCutLocusStructure

/-! One fixed joined development covers a whole original edge. Its source
list is finite independently of the neighborhood chosen around each target. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ H : P.Face, (H.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (H.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- A whole original edge contains only finitely many nonvertex junctions. -/
theorem edge_junctions_finite (a : frontier P.body) (F G : P.Face)
    (shared : P.ShareEdge F G) :
    {b : frontier P.body | a ≠ b ∧ (b : Space) ∈ F.val ∩ G.val ∧
      (b : Space) ∉ P.vertices ∧ 2 < Nat.card (P.geodesicFiber a b)}.Finite := by
  obtain ⟨center, inside⟩ := P.solid
  obtain ⟨facets⟩ := P.exists_normalized_facets inside
  obtain ⟨chart⟩ := exists_edge_folding facets F G shared
  let junctions : Set (frontier P.body) := {b | a ≠ b ∧ (b : Space) ∈ F.val ∩ G.val ∧
    (b : Space) ∉ P.vertices ∧ 2 < Nat.card (P.geodesicFiber a b)}
  have image_finite : ((fun b : frontier P.body => chart.unfold b) '' junctions).Finite := by
    apply (finite_three_site_centers (chart.sourceImages a) (chart.sourceImages_finite a)).subset
    rintro _ ⟨b, hb, rfl⟩
    obtain ⟨patch⟩ := chart.exists_metric_patch shared hb.2.1 hb.2.2.1
    have count : 2 < (chart.activeSources a b).ncard := by
      rw [patch.activeSources_ncard graph small_faces a b hb.1 patch.center_mem]
      exact hb.2.2.2
    obtain ⟨p, hp, q, hq, r, hr, pq, pr, qr⟩ :=
      (two_lt_ncard (patch.activeSources_finite graph small_faces a b hb.1 patch.center_mem)).mp count
    have subset := patch.activeSources_subset graph small_faces a b hb.1 patch.center_mem
    have pvalue := chart.activeSource_distance patch a b patch.center_mem p hp
    exact ⟨p, subset hp, q, subset hq, r, subset hr, pq, pr, qr,
      pvalue.symm.trans (chart.activeSource_distance patch a b patch.center_mem q hq),
      pvalue.symm.trans (chart.activeSource_distance patch a b patch.center_mem r hr)⟩
  apply image_finite.of_finite_image
  intro b hb c hc same
  apply Subtype.ext
  change chart.unfold b = chart.unfold c at same
  have equal := congrArg chart.fold.map same
  rwa [chart.fold_unfold (Or.inl hb.2.1.1), chart.fold_unfold (Or.inl hc.2.1.1)] at equal

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
