import SixVertexUnfolding.Geometry.FlatChartRegions

/-! Every smaller coordinate disk still contains an actual surface
neighborhood of the chart center. -/

namespace SixVertexUnfolding.ConvexPolyhedron.FlatChart

open Set Filter Topology

variable {P : ConvexPolyhedron} {z : Space} (chart : P.FlatChart z)

theorem exists_coordinate_neighborhood (b : frontier P.body) (at_center : (b : Space) = z)
    {radius : ℝ} (positive : 0 < radius) :
    ∃ δ > 0, ∀ c : frontier P.body, dist (c : Space) (b : Space) < δ →
      (c : Space) ∈ chart.map '' chart.domain ∧
      dist (chart.coordinates c) chart.origin < radius := by
  obtain ⟨U, openU, center, covered⟩ := chart.covers
  have image_near : ∀ᶠ c : frontier P.body in 𝓝 b, (c : Space) ∈ chart.map '' chart.domain := by
    apply mem_of_superset ((openU.preimage continuous_subtype_val).mem_nhds
      (show (b : Space) ∈ U from at_center.symm ▸ center))
    intro c hc
    exact covered ⟨hc, c.property⟩
  have center_coordinates : chart.coordinates b = chart.origin := by
    rw [show (b : Space) = chart.map chart.origin from at_center.trans chart.at_origin.symm]
    exact chart.coordinates_map chart.origin_mem
  have coordinates_near : ∀ᶠ c : frontier P.body in 𝓝 b,
      dist (chart.coordinates c) chart.origin < radius := by
    have near := Metric.tendsto_nhds.mp (chart.coordinates_continuousAt_center b at_center) radius positive
    simpa only [center_coordinates] using near
  obtain ⟨δ, dp, near⟩ := Metric.eventually_nhds_iff.mp (image_near.and coordinates_near)
  exact ⟨δ, dp, fun c hc => near hc⟩

end SixVertexUnfolding.ConvexPolyhedron.FlatChart
