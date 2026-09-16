import SixVertexUnfolding.Geometry.EdgeLocalMinimum
import SixVertexUnfolding.Geometry.EdgeMinimumRouteUniqueness
import SixVertexUnfolding.Geometry.MultipleRouteTopology
import SixVertexUnfolding.Geometry.VoronoiDiagram

/-! The actual multiple-route locus is exactly a local Voronoi boundary
in the joined development, including across an original edge. -/

namespace SixVertexUnfolding.ConvexPolyhedron.EdgeFolding.MetricPatch

open Set

variable {P : ConvexPolyhedron} {center z : Space} {facets : P.NormalizedFacets center}
  {F G : P.Face} {chart : EdgeFolding facets F G} (patch : chart.MetricPatch z)
  (graph : P.SixVertexGraph)
  (small_faces : ∀ H : P.Face, (H.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (H.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- Nearby multiple-route points are exactly ties between nearest old active sources on both sides of the crease. -/
theorem local_voronoi_cut_locus (a b : frontier P.body) (different : a ≠ b) (target : (b : Space) ∈ patch.domain) :
    ∃ V : Set Space, IsOpen V ∧ (b : Space) ∈ V ∧ V ⊆ patch.domain ∧ ∀ x ∈ V ∩ frontier P.body,
      (x ∈ P.multipleRouteLocus a ↔ chart.unfold x ∈ voronoiBoundary (chart.activeSources a b)) := by
  obtain ⟨U, openU, bU, contained, minimum⟩ := patch.local_minimum_distance graph small_faces a b different target
  refine ⟨U ∩ ({(a : Space)}ᶜ : Set Space), openU.inter isClosed_singleton.isOpen_compl,
    ⟨bU, fun same => different (Subtype.ext same.symm)⟩, inter_subset_left.trans contained, ?_⟩
  intro x hx
  let c : frontier P.body := ⟨x, hx.2⟩
  have distinct_c : a ≠ c := fun same => hx.1.2 (congrArg Subtype.val same.symm)
  have criterion := patch.unique_route_iff_unique_minimum graph small_faces a c distinct_c (contained hx.1.1)
    (chart.activeSources a b) (patch.activeSources_finite graph small_faces a b different target)
    U openU hx.1.1 contained minimum
  have value := minimum x ⟨hx.1.1, hx.2⟩
  have ties := mem_voronoiBoundary_iff_multiple_minima (chart.activeSources a b) (chart.unfold x)
    (P.surfaceDist a x) value.1 value.2
  change (c : Space) ∈ P.multipleRouteLocus a ↔ _
  rw [P.multiple_routes_iff_fiber a c, and_iff_right distinct_c]
  exact criterion.not.trans ties.symm

end SixVertexUnfolding.ConvexPolyhedron.EdgeFolding.MetricPatch
