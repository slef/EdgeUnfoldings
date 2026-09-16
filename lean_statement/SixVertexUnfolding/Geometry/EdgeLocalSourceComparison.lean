import SixVertexUnfolding.Geometry.EdgeMetricPatch
import SixVertexUnfolding.Geometry.LocalSourceComparison

/-! A distance comparison touching at a point of a metric edge patch
identifies the sources; both sides of the crease provide a full planar neighborhood. -/

namespace SixVertexUnfolding.ConvexPolyhedron.EdgeFolding.MetricPatch

open Set

variable {P : ConvexPolyhedron} {center z : Space} {facets : P.NormalizedFacets center}
  {F G : P.Face} {chart : EdgeFolding facets F G} (patch : chart.MetricPatch z)

theorem local_source_comparison_eq (x : frontier P.body) (inside : (x : Space) ∈ patch.domain) (p q : Plane)
    (U : Set Space) (openU : IsOpen U) (xU : (x : Space) ∈ U)
    (comparison : ∀ y ∈ U ∩ frontier P.body, dist p (chart.unfold y) ≤ dist q (chart.unfold y))
    (equal : dist p (chart.unfold x) = dist q (chart.unfold x)) : p = q := by
  let V := patch.sheet.domain ∩ chart.fold.map ⁻¹' U
  have openV : IsOpen V := patch.sheet.open_domain.inter (openU.preimage chart.fold.continuous)
  have xV : chart.unfold x ∈ V := by
    refine ⟨patch.unfold_mem ⟨inside, x.property⟩, ?_⟩
    change chart.fold.map (chart.unfold x) ∈ U
    rwa [chart.fold_unfold (patch.on_facets ⟨inside, x.property⟩)]
  apply SixVertexUnfolding.local_source_comparison_eq p q (chart.unfold x) V openV xV ?_ equal
  intro y hy
  have surface := patch.sheet.on_surface ⟨y, hy.1, rfl⟩
  simpa only [Neighborhood.unfold_fold chart patch.sheet hy.1] using comparison _ ⟨hy.2, surface⟩

end SixVertexUnfolding.ConvexPolyhedron.EdgeFolding.MetricPatch
