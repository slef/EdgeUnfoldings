import SixVertexUnfolding.Geometry.EdgeMetricPatch

/-! The terminal chord in a metric edge patch gives the exact full route
distance, not merely a planar lower bound. -/

namespace SixVertexUnfolding.ConvexPolyhedron.EdgeFolding

open Set

variable {P : ConvexPolyhedron} {center : Space} {facets : P.NormalizedFacets center}
  {F G : P.Face} (chart : EdgeFolding facets F G)

theorem recoveredSource_coordinates (t : unitInterval) (before : t < 1) (f : P.BoundaryCurve) :
    chart.unfold (f t) = AffineMap.lineMap (chart.recoveredSource t f) (chart.unfold (f 1)) (t : ℝ) := by
  have nonzero : 1 - (t : ℝ) ≠ 0 := ne_of_gt (sub_pos.mpr (show (t : ℝ) < 1 from before))
  rw [AffineMap.lineMap_apply_module, recoveredSource, smul_smul, mul_inv_cancel₀ nonzero, one_smul, sub_add_cancel]

theorem recoveredSource_distance {z : Space} (patch : chart.MetricPatch z)
    (f : P.BoundaryCurve) (geodesic : f ∈ P.geodesicCurves) (t : unitInterval) (before : t < 1)
    (inside : (f t : Space) ∈ patch.domain) (target : (f 1 : Space) ∈ patch.domain) :
    P.surfaceDist (f 0) (f 1) = dist (chart.recoveredSource t f) (chart.unfold (f 1)) := by
  have portion := geodesic t 1
  rw [patch.metric _ ⟨inside, (f t).property⟩ _ ⟨target, (f 1).property⟩,
    chart.recoveredSource_coordinates t before f, dist_lineMap_right] at portion
  have elapsed : dist t (1 : unitInterval) = 1 - (t : ℝ) := by
    change dist (t : ℝ) (1 : ℝ) = _
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr t.property.2)]
    ring
  rw [elapsed, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr t.property.2)] at portion
  have positive : 0 < 1 - (t : ℝ) := sub_pos.mpr (show (t : ℝ) < 1 from before)
  nlinarith

/-- An actual terminal source in the patch gives the full intrinsic distance. -/
theorem terminal_source_distance {z : Space} (patch : chart.MetricPatch z)
    (f : P.BoundaryCurve) (geodesic : f ∈ P.geodesicCurves)
    (source : Plane) (terminal : chart.HasTerminalSource f source) (target : (f 1 : Space) ∈ patch.domain) :
    P.surfaceDist (f 0) (f 1) = dist source (chart.unfold (f 1)) := by
  let path := P.surfacePathOfCurve f
  obtain ⟨t, _, before, inside, _⟩ := path.common_time_near_target path patch.domain patch.open_domain target
  rw [chart.recoveredSource_distance patch f geodesic t before inside target,
    chart.recoveredSource_of_terminal f geodesic source terminal patch.domain patch.open_domain target patch.metric t before inside]

/-- The same source gives every radial prefix distance in the joined development. -/
theorem terminal_source_distance_at {z : Space} (patch : chart.MetricPatch z)
    (f : P.BoundaryCurve) (geodesic : f ∈ P.geodesicCurves)
    (source : Plane) (terminal : chart.HasTerminalSource f source) (target : (f 1 : Space) ∈ patch.domain)
    (t : unitInterval) (coordinates : chart.unfold (f t) = AffineMap.lineMap source (chart.unfold (f 1)) (t : ℝ)) :
    P.surfaceDist (f 0) (f t) = dist source (chart.unfold (f t)) := by
  rw [geodesic 0 t, chart.terminal_source_distance patch f geodesic source terminal target,
    coordinates, dist_left_lineMap, Real.norm_eq_abs, abs_of_nonneg t.property.1]
  have elapsed : dist (0 : unitInterval) t = (t : ℝ) := by
    change dist (0 : ℝ) (t : ℝ) = _
    rw [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg t.property.1]
  rw [elapsed, mul_comm]

end SixVertexUnfolding.ConvexPolyhedron.EdgeFolding
