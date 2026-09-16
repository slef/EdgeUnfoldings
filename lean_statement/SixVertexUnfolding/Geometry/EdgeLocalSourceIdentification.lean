import SixVertexUnfolding.Geometry.EdgeRouteSourceNeighborhoods

/-! A local distance formula at a proper terminal point must use the source
of the original route, even when that point lies on the shared edge. -/

namespace SixVertexUnfolding.ConvexPolyhedron.EdgeFolding.MetricPatch

open Set

variable {P : ConvexPolyhedron} {center z : Space} {facets : P.NormalizedFacets center}
  {F G : P.Face} {chart : EdgeFolding facets F G} (patch : chart.MetricPatch z)

theorem local_formula_identifies_source (f : P.BoundaryCurve) (geodesic : f ∈ P.geodesicCurves)
    (source other : Plane) (terminal : chart.HasTerminalSource f source) (target : (f 1 : Space) ∈ patch.domain)
    (m : unitInterval) (positive : 0 < m) (before : m < 1) (inside : (f m : Space) ∈ patch.domain)
    (U : Set Space) (openU : IsOpen U) (fmU : (f m : Space) ∈ U)
    (formula : ∀ x ∈ U ∩ frontier P.body, P.surfaceDist (f 0) x = dist other (chart.unfold x)) : other = source := by
  let path := P.surfacePathOfCurve f
  obtain ⟨shortest, finite, speed⟩ := P.surfacePathOfCurve_shortest f geodesic
  obtain ⟨s, v, sm, mv, near⟩ := path.interval_inside_neighborhood m positive before (U ∩ patch.domain)
    (openU.inter patch.open_domain) ⟨fmU, inside⟩
  obtain ⟨u, mu, uv⟩ := exists_between mv
  have u_before : u < 1 := uv.trans_le unitInterval.le_one'
  have fuU : (f u : Space) ∈ U ∩ patch.domain := near u ⟨sm.le.trans mu.le, uv.le⟩
  have at_m := chart.terminal_formula_extends f geodesic source terminal patch.domain patch.open_domain target patch.metric m before inside
  have at_u := chart.terminal_formula_extends f geodesic source terminal patch.domain patch.open_domain target patch.metric u u_before fuU.2
  have source_distance (r : unitInterval) : P.surfaceDist (f 0) (f r) = path.length.toReal * (r : ℝ) :=
    path.source_distance shortest finite speed r
  have between : dist (chart.unfold (f m)) (chart.unfold (f u)) = path.length.toReal * ((u : ℝ) - (m : ℝ)) := by
    rw [← patch.metric _ ⟨inside, (f m).property⟩ _ ⟨fuU.2, (f u).property⟩]
    change P.surfaceDist (path.curve m) (path.curve u) = _
    rw [path.surfaceDist_along shortest finite speed]
    congr 1
    change dist (m : ℝ) (u : ℝ) = _
    rw [Real.dist_eq, abs_of_neg (sub_neg.mpr (show (m : ℝ) < u from mu))]
    ring
  have radial (q : Plane) (first : dist q (chart.unfold (f m)) = path.length.toReal * (m : ℝ))
      (last : dist q (chart.unfold (f u)) = path.length.toReal * (u : ℝ)) :
      chart.unfold (f m) = AffineMap.lineMap q (chart.unfold (f u)) ((m : ℝ) / (u : ℝ)) := by
    simpa only [sub_zero] using point_eq_lineMap_of_distance_ratios q (chart.unfold (f u)) (chart.unfold (f m))
      0 m u path.length.toReal (positive.trans mu) m.property.1 mu.le
      (by simpa using first) between (by simpa using last)
  have actual := radial source
    ((chart.terminal_source_distance_at patch f geodesic source terminal target m at_m).symm.trans (source_distance m))
    ((chart.terminal_source_distance_at patch f geodesic source terminal target u at_u).symm.trans (source_distance u))
  have candidate := radial other ((formula _ ⟨fmU, (f m).property⟩).symm.trans (source_distance m))
    ((formula _ ⟨fuU.1, (f u).property⟩).symm.trans (source_distance u))
  have ratio_before : (m : ℝ) / (u : ℝ) < 1 := (div_lt_one (show 0 < (u : ℝ) from positive.trans mu)).mpr mu
  exact lineMap_left_unique other source (chart.unfold (f u)) _ ratio_before.ne (candidate.symm.trans actual)

end SixVertexUnfolding.ConvexPolyhedron.EdgeFolding.MetricPatch
