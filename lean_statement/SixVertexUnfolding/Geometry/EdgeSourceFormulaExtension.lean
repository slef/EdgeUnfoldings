import SixVertexUnfolding.Geometry.EdgeMetricPatch
import SixVertexUnfolding.Geometry.GeodesicCurvePaths

/-! Extend a local source formula by actual surface paths in a metric edge
patch. Both nearby endpoints and the joining segment may cross the crease. -/

namespace SixVertexUnfolding.ConvexPolyhedron.EdgeFolding.MetricPatch

open Set Filter
open scoped Topology

variable {P : ConvexPolyhedron} {center z : Space} {facets : P.NormalizedFacets center}
  {F G : P.Face} {chart : EdgeFolding facets F G} (patch : chart.MetricPatch z)

/-- A local radial formula extends to exact-length competitors near any later target in this patch. -/
theorem source_formula_extension (a b m : frontier P.body)
    (bU : (b : Space) ∈ patch.domain) (mU : (m : Space) ∈ patch.domain) (source : Plane)
    (t : ℝ) (positive : 0 < t) (before : t < 1)
    (on_ray : chart.unfold m = AffineMap.lineMap source (chart.unfold b) t)
    (U : Set Space) (openU : IsOpen U) (mV : (m : Space) ∈ U)
    (formula : ∀ x ∈ U ∩ frontier P.body, P.surfaceDist a x = dist source (chart.unfold x)) :
    ∃ V : Set Space, IsOpen V ∧ (b : Space) ∈ V ∧ ∀ x ∈ V ∩ frontier P.body,
      ∃ path : P.SurfacePath a x, path.length ≠ ⊤ ∧ path.length.toReal = dist source (chart.unfold x) := by
  let middle (c : frontier P.body) := AffineMap.lineMap source (chart.unfold c) t
  let T : Set (frontier P.body) := Subtype.val ⁻¹' patch.domain
  have openT : IsOpen T := patch.open_domain.preimage continuous_subtype_val
  have coordinates : ContinuousOn (fun c : frontier P.body => chart.unfold c) T :=
    patch.unfold_continuousOn.comp continuous_subtype_val.continuousOn (fun c hc => ⟨hc, c.property⟩)
  have continuous_middle : ContinuousAt middle b := by
    simp only [middle, AffineMap.lineMap_apply_module]
    exact continuousAt_const.add (continuousAt_const.smul (coordinates.continuousAt (openT.mem_nhds bU)))
  let Y : Set Plane := patch.sheet.domain ∩ chart.fold.map ⁻¹' (U ∩ patch.domain)
  have openY : IsOpen Y := patch.sheet.open_domain.inter ((openU.inter patch.open_domain).preimage chart.fold.continuous)
  have middle_b : middle b = chart.unfold m := on_ray.symm
  have middle_in : middle b ∈ Y := by
    rw [middle_b]
    exact ⟨patch.unfold_mem ⟨mU, m.property⟩,
      by simpa only [mem_preimage, chart.fold_unfold (patch.on_facets ⟨mU, m.property⟩)] using (show (m : Space) ∈ U ∩ patch.domain from ⟨mV, mU⟩)⟩
  have inT : ∀ᶠ c : frontier P.body in 𝓝 b, c ∈ T := openT.mem_nhds bU
  have near : ∀ᶠ c : frontier P.body in 𝓝 b, c ∈ T ∧ middle c ∈ Y :=
    inT.and (continuous_middle.eventually (openY.mem_nhds middle_in))
  obtain ⟨N, subset, openN, bN⟩ := mem_nhds_iff.mp near
  obtain ⟨V, openV, sameV⟩ := isOpen_induced_iff.mp openN
  refine ⟨V, openV, ?_, ?_⟩
  · rw [← sameV] at bN
    exact bN
  · intro x hx
    let c : frontier P.body := ⟨x, hx.2⟩
    have cN : c ∈ N := sameV ▸ hx.1
    have allowed := subset cN
    let w := chart.fold.map (middle c)
    have w_surface : w ∈ frontier P.body := patch.sheet.on_surface ⟨middle c, allowed.2.1, rfl⟩
    have w_coordinates : chart.unfold w = middle c := Neighborhood.unfold_fold chart patch.sheet allowed.2.1
    obtain ⟨front, front_shortest, front_finite, _⟩ := P.exists_shortest_lipschitz_surface_path a.property w_surface
    obtain ⟨last, last_shortest, last_finite, _⟩ := P.exists_shortest_lipschitz_surface_path w_surface hx.2
    have front_length : front.length.toReal = dist source (middle c) := by
      rw [front.length_eq_surfaceEDist front_shortest]
      exact (formula w ⟨allowed.2.2.1, w_surface⟩).trans (congrArg (dist source) w_coordinates)
    have last_length : last.length.toReal = dist (middle c) (chart.unfold x) := by
      rw [last.length_eq_surfaceEDist last_shortest]
      exact (patch.metric w ⟨allowed.2.2.2, w_surface⟩ x ⟨allowed.1, hx.2⟩).trans
        (congrArg (fun y => dist y (chart.unfold x)) w_coordinates)
    refine ⟨front.join last, front.join_finite last front_finite last_finite, ?_⟩
    calc
      (front.join last).length.toReal = (front.length + last.length).toReal := congrArg ENNReal.toReal (front.join_length last)
      _ = front.length.toReal + last.length.toReal := ENNReal.toReal_add front_finite last_finite
      _ = dist source (chart.unfold x) := by
        rw [front_length, last_length]
        change dist source (AffineMap.lineMap source (chart.unfold x) t) +
          dist (AffineMap.lineMap source (chart.unfold x) t) (chart.unfold x) = _
        rw [dist_left_lineMap, dist_lineMap_right, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg positive.le, abs_of_nonneg (sub_nonneg.mpr before.le)]
        ring

end SixVertexUnfolding.ConvexPolyhedron.EdgeFolding.MetricPatch
