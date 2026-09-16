import SixVertexUnfolding.Geometry.LineVoronoiPersistence
import SixVertexUnfolding.Geometry.EdgeLocalVoronoi

/-! The same finite-crossing criterion controls straight segments that
lie along an original edge. A single joined development is fixed throughout. -/

namespace SixVertexUnfolding.ConvexPolyhedron.EdgeFolding

open Set

variable {P : ConvexPolyhedron} {center : Space} {facets : P.NormalizedFacets center}
  {F G : P.Face} (chart : EdgeFolding facets F G) (graph : P.SixVertexGraph)
  (small_faces : ∀ H : P.Face, (H.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (H.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
theorem cut_persists_along_line (a : frontier P.body) (shared : P.ShareEdge F G)
    (curve : ℝ →ᵃ[ℝ] Space) {t : ℝ} (target : curve t ∈ F.val ∩ G.val)
    (not_vertex : curve t ∉ P.vertices) (cut : curve t ∈ P.multipleRouteLocus a)
    (regular : t ∉ lineSourceCrossings (chart.sourceImages a) (chart.left.comp curve)) :
    ∃ J : Set ℝ, IsOpen J ∧ t ∈ J ∧ ∀ s ∈ J, curve s ∈ F.val → curve s ∈ P.multipleRouteLocus a := by
  let b : frontier P.body := ⟨curve t, F.subset_frontier target.1⟩
  have different : a ≠ b := ((P.multiple_routes_iff_fiber a b).mp cut).1
  obtain ⟨patch⟩ := chart.exists_metric_patch shared target not_vertex
  obtain ⟨V, openV, bV, _, diagram⟩ := patch.local_voronoi_cut_locus graph small_faces a b different patch.center_mem
  have coordinate : chart.unfold b = (chart.left.comp curve) t := chart.unfold_of_first target.1
  have contained := patch.activeSources_subset graph small_faces a b different patch.center_mem
  have common (p : Plane) (hp : p ∈ chart.activeSources a b) (q : Plane) (hq : q ∈ chart.activeSources a b) :
      dist p ((chart.left.comp curve) t) = dist q ((chart.left.comp curve) t) := by
    rw [← coordinate]
    exact (chart.activeSource_distance patch a b patch.center_mem p hp).symm.trans
      (chart.activeSource_distance patch a b patch.center_mem q hq)
  have boundary : (chart.left.comp curve) t ∈ voronoiBoundary (chart.activeSources a b) := by
    rw [← coordinate]
    exact (diagram _ ⟨bV, b.property⟩).mp cut
  have all_tied := voronoi_ties_persist_on_line (chart.sourceImages a) (chart.activeSources a b)
    contained (chart.left.comp curve) regular common boundary
  refine ⟨curve ⁻¹' V, openV.preimage curve.continuous_of_finiteDimensional, bV, ?_⟩
  intro s hs in_face
  apply (diagram _ ⟨hs, F.subset_frontier in_face⟩).mpr
  rw [chart.unfold_of_first in_face]
  exact all_tied s

end SixVertexUnfolding.ConvexPolyhedron.EdgeFolding
