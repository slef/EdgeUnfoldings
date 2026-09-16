import SixVertexUnfolding.Geometry.EdgeTerminalSources
import SixVertexUnfolding.Geometry.EdgeMetricNeighborhood
import SixVertexUnfolding.Geometry.TerminalInterpolation

/-! A terminal source can be recovered from any earlier visit to a sufficiently
small edge neighborhood, even when the route visits both incident faces. -/

namespace SixVertexUnfolding.ConvexPolyhedron.EdgeFolding

open Set Filter
open scoped Topology

variable {P : ConvexPolyhedron} {center : Space} {facets : P.NormalizedFacets center}
  {F G : P.Face} (chart : EdgeFolding facets F G)

/-- The common source recovered by extending a developed terminal chord back to time zero. -/
noncomputable def recoveredSource (t : unitInterval) (f : P.BoundaryCurve) : Plane :=
  (1 - (t : ℝ))⁻¹ • (chart.unfold (f t) - (t : ℝ) • chart.unfold (f 1))

theorem recoveredSource_eq (t : unitInterval) (before : t < 1) (f : P.BoundaryCurve) (source : Plane)
    (formula : chart.unfold (f t) = AffineMap.lineMap source (chart.unfold (f 1)) (t : ℝ)) :
    chart.recoveredSource t f = source := by
  have nonzero : 1 - (t : ℝ) ≠ 0 := ne_of_gt (sub_pos.mpr (show (t : ℝ) < 1 from before))
  unfold recoveredSource
  rw [formula, AffineMap.lineMap_apply_module, add_sub_cancel_right, inv_smul_smul₀ nonzero]

/-- A terminal formula extends backwards to any visit in an isometric edge neighborhood. -/
theorem terminal_formula_extends (f : P.BoundaryCurve) (geodesic : f ∈ P.geodesicCurves)
    (source : Plane) (terminal : chart.HasTerminalSource f source)
    (U : Set Space) (openU : IsOpen U) (targetU : (f 1 : Space) ∈ U)
    (metric : ∀ x ∈ U ∩ frontier P.body, ∀ y ∈ U ∩ frontier P.body,
      P.surfaceDist x y = dist (chart.unfold x) (chart.unfold y))
    (t : unitInterval) (before : t < 1) (inside : (f t : Space) ∈ U) :
    chart.unfold (f t) = AffineMap.lineMap source (chart.unfold (f 1)) (t : ℝ) := by
  obtain ⟨start, start_before, tail⟩ := terminal
  let path := P.surfacePathOfCurve f
  have late : ∀ᶠ r : ℝ in 𝓝 1, max (start : ℝ) (t : ℝ) < r := Ioi_mem_nhds (max_lt start_before before)
  have near : ∀ᶠ r : ℝ in 𝓝 1, path.curve.extend r ∈ U :=
    path.curve.continuous_extend.continuousAt.eventually (openU.mem_nhds (by simpa using targetU))
  obtain ⟨r, r_before, after, inU⟩ := (late.and near).exists_lt
  let u : unitInterval := ⟨r, (start.property.1.trans_lt ((le_max_left _ _).trans_lt after)).le, r_before.le⟩
  have uU : (f u : Space) ∈ U := by
    change path.curve.extend (u : ℝ) ∈ U at inU
    rw [Path.extend_apply path.curve u.property] at inU
    exact inU
  have tu : t < u := (le_max_right (start : ℝ) (t : ℝ)).trans_lt after
  have distances (v w : unitInterval) (vU : (f v : Space) ∈ U) (wU : (f w : Space) ∈ U) (vw : v ≤ w) :
      dist (chart.unfold (f v)) (chart.unfold (f w)) = P.surfaceDist (f 0) (f 1) * ((w : ℝ) - (v : ℝ)) := by
    rw [← metric _ ⟨vU, (f v).property⟩ _ ⟨wU, (f w).property⟩, geodesic v w]
    congr 1
    change dist (v : ℝ) (w : ℝ) = _
    rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (show (v : ℝ) ≤ (w : ℝ) from vw))]
  have affine := point_eq_lineMap_of_distance_ratios (chart.unfold (f t)) (chart.unfold (f 1)) (chart.unfold (f u))
    (t : ℝ) (u : ℝ) 1 (P.surfaceDist (f 0) (f 1)) before tu.le r_before.le
    (distances t u inside uU tu.le) (distances u 1 uU targetU r_before.le)
    (distances t 1 inside targetU before.le)
  have at_u := (tail u ⟨(le_max_left (start : ℝ) (t : ℝ)).trans after.le, r_before.le⟩).2
  exact terminal_interpolation_unique source (chart.unfold (f 1)) (chart.unfold (f t)) t u before r_before
    (affine.symm.trans at_u)

/-- Recovery from any such visit gives the actual terminal source. -/
theorem recoveredSource_of_terminal (f : P.BoundaryCurve) (geodesic : f ∈ P.geodesicCurves)
    (source : Plane) (terminal : chart.HasTerminalSource f source)
    (U : Set Space) (openU : IsOpen U) (targetU : (f 1 : Space) ∈ U)
    (metric : ∀ x ∈ U ∩ frontier P.body, ∀ y ∈ U ∩ frontier P.body,
      P.surfaceDist x y = dist (chart.unfold x) (chart.unfold y))
    (t : unitInterval) (before : t < 1) (inside : (f t : Space) ∈ U) :
    chart.recoveredSource t f = source :=
  chart.recoveredSource_eq t before f source
    (chart.terminal_formula_extends f geodesic source terminal U openU targetU metric t before inside)

end SixVertexUnfolding.ConvexPolyhedron.EdgeFolding
