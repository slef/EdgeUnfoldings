import SixVertexUnfolding.Geometry.EdgeMetricNeighborhood
import SixVertexUnfolding.Geometry.EdgeTerminalRecovery

/-! A reusable actual neighborhood of an edge: metric coordinates and a
planar sheet on which nearby straight segments can be folded onto the surface. -/

namespace SixVertexUnfolding.ConvexPolyhedron.EdgeFolding

open Set

variable {P : ConvexPolyhedron} {center : Space} {facets : P.NormalizedFacets center}
  {F G : P.Face} (chart : EdgeFolding facets F G)

/-- The geometric data needed to extend routes through either side of an original edge. -/
structure MetricPatch (z : Space) where
  domain : Set Space
  open_domain : IsOpen domain
  center_mem : z ∈ domain
  sheet : chart.Neighborhood z
  covered : domain ∩ frontier P.body ⊆ chart.fold.map '' sheet.domain
  only_two : ∀ x ∈ domain, ∀ H : P.Face, x ∈ H.val → H = F ∨ H = G
  metric : ∀ x ∈ domain ∩ frontier P.body, ∀ y ∈ domain ∩ frontier P.body,
    P.surfaceDist x y = dist (chart.unfold x) (chart.unfold y)

/-- Every nonvertex edge point has this metric patch, constructed from the original facets. -/
theorem exists_metric_patch (shared : P.ShareEdge F G) {z : Space}
    (hz : z ∈ F.val ∩ G.val) (not_vertex : z ∉ P.vertices) : Nonempty (chart.MetricPatch z) := by
  obtain ⟨sheet⟩ := chart.exists_neighborhood shared hz not_vertex
  obtain ⟨U, openU, zU, only_two, _, metric⟩ := chart.exists_metric_neighborhood shared hz not_vertex
  obtain ⟨V, openV, zV, covers⟩ := sheet.covers
  exact ⟨{
    domain := U ∩ V
    open_domain := openU.inter openV
    center_mem := ⟨zU, zV⟩
    sheet := sheet
    covered := fun _ hx => covers ⟨hx.1.2, hx.2⟩
    only_two := fun x hx H hH => only_two x hx.1 H hH
    metric := fun x hx y hy => metric x ⟨hx.1.1, hx.2⟩ y ⟨hy.1.1, hy.2⟩ }⟩

namespace MetricPatch

variable {chart} {z : Space} (patch : chart.MetricPatch z)

theorem on_facets : patch.domain ∩ frontier P.body ⊆ F.val ∪ G.val := by
  intro x hx
  obtain ⟨H, xH⟩ := P.boundary_point_in_face hx.2
  rcases patch.only_two x hx.1 H xH with rfl | rfl
  exacts [Or.inl xH, Or.inr xH]

theorem unfold_mem {x : Space} (hx : x ∈ patch.domain ∩ frontier P.body) :
    chart.unfold x ∈ patch.sheet.domain := by
  obtain ⟨p, hp, rfl⟩ := patch.covered hx
  rwa [Neighborhood.unfold_fold chart patch.sheet hp]

theorem unfold_continuousOn : ContinuousOn chart.unfold (patch.domain ∩ frontier P.body) :=
  chart.unfold_continuousOn.mono patch.on_facets

end MetricPatch
end SixVertexUnfolding.ConvexPolyhedron.EdgeFolding
