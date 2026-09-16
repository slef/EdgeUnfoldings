import SixVertexUnfolding.Geometry.FlatChartRegions
import SixVertexUnfolding.Geometry.CofacialStarCuts

/-! Removing the closed star cuts leaves a small disk in every
flat chart centered at a retained surface point. -/

namespace SixVertexUnfolding.ConvexPolyhedron.FlatChart

open Set Filter Topology

variable {P : ConvexPolyhedron} {z : Space} (chart : P.FlatChart z)

theorem exists_uncut_disk (a b : frontier P.body) (at_center : (b : Space) = z)
    (outside : b ∉ P.starCuts a) :
    ∃ radius > 0, ∃ contained : Metric.ball chart.origin radius ⊆ chart.domain,
      ∀ x : Metric.ball chart.origin radius,
        (⟨chart.map x, chart.on_surface (contained x.property)⟩ : frontier P.body) ∉ P.starCuts a := by
  let region := chart.pullback ((P.starCuts a)ᶜ)
  have open_region : IsOpen region := chart.pullback_open (P.starCuts_closed a).isOpen_compl
  have centered : chart.surfaceMap ⟨chart.origin, chart.origin_mem⟩ = b :=
    Subtype.ext (chart.at_origin.trans at_center.symm)
  have center : chart.origin ∈ region := by
    apply (chart.mem_pullback _ _ chart.origin_mem).mpr
    change chart.surfaceMap ⟨chart.origin, chart.origin_mem⟩ ∉ P.starCuts a
    rw [centered]
    exact outside
  obtain ⟨radius, positive, disk⟩ := Metric.isOpen_iff.mp open_region chart.origin center
  have contained : Metric.ball chart.origin radius ⊆ chart.domain := by
    intro x hx
    obtain ⟨y, _, same⟩ := disk hx
    exact same ▸ y.property
  refine ⟨radius, positive, contained, ?_⟩
  intro x
  exact (chart.mem_pullback _ _ (contained x.property)).mp (disk x.property)

end SixVertexUnfolding.ConvexPolyhedron.FlatChart
