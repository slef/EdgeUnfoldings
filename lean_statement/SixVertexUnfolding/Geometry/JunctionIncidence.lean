import SixVertexUnfolding.Geometry.JunctionSourceOrder
import SixVertexUnfolding.Geometry.CutGraphCircle
import SixVertexUnfolding.Geometry.CutGraphOpenEdges

/-! Gap rays and actual incident cut-graph edges have the same small-circle
crossings. One bijection retains the geometric location along every short
positive portion of each ray, independently of the sampling radius.
-/

namespace SixVertexUnfolding.ConvexPolyhedron.CutVoronoiChart

open Real Set

variable {P : ConvexPolyhedron} {a b : frontier P.body} (chart : P.CutVoronoiChart a b)

/-- The angular gap list parametrizes every actual cut point on each sufficiently
small circle. Original vertices are explicitly excluded from this neighborhood. -/
theorem midpoints_equiv_circle (K : P.EmbeddedCutGraph a) (vertex : (b : Space) ∈ K.vertices)
    (different : a ≠ b) (not_vertex : (b : Space) ∉ P.vertices)
    (sites : Fin chart.sources.ncard ≃ chart.sources) (θ : Fin chart.sources.ncard → ℝ)
    (increasing : StrictMono θ) (bounds : ∀ i, 0 ≤ θ i ∧ θ i < 2 * π)
    (position : ∀ i, (sites i : Plane) = chart.origin + P.surfaceDist a b • direction (θ i))
    (first last : Fin chart.sources.ncard) (at_first : first.val = 0)
    (at_last : last.val + 1 = chart.sources.ncard) (two : first < last) :
    ∃ ε > 0, ∀ ρ ∈ Ioo (0 : ℝ) ε,
      ∃ e : circularGapMidpoints θ first last ≃
        K.circleTrace (u := ⟨b, vertex⟩) chart.toFlatChart ρ,
        ∀ m, (e m : Plane) = chart.origin + ρ • direction m := by
  classical
  have radius_positive : 0 < P.surfaceDist a b := by
    have positive := tail_radius_pos different (0 : unitInterval) (by change (0 : ℝ) < 1; norm_num)
    simpa using positive
  have openD := chart.open_domain.inter
    (P.vertices.finite_toSet.isClosed.isOpen_compl.preimage chart.continuous)
  have center : chart.origin ∈ chart.domain ∩ chart.map ⁻¹' (P.vertices : Set Space)ᶜ :=
    ⟨chart.origin_mem, by change chart.map chart.origin ∉ P.vertices; rwa [chart.at_origin]⟩
  obtain ⟨ε, positive, disk⟩ := Metric.isOpen_iff.mp openD chart.origin center
  refine ⟨ε, positive, ?_⟩
  intro ρ hr
  have circle (m : ℝ) : dist (chart.origin + ρ • direction m) chart.origin = ρ := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, direction_norm, mul_one,
      Real.norm_eq_abs, abs_of_pos hr.1]
  have inside (m : ℝ) : chart.origin + ρ • direction m ∈ chart.domain :=
    (disk (show chart.origin + ρ • direction m ∈ Metric.ball chart.origin ε by
      change dist _ _ < ε
      rw [circle]
      exact hr.2)).1
  have on_cut (m : circularGapMidpoints θ first last) :
      chart.map (chart.origin + ρ • direction m) ∈ P.cutSetInSpace a := by
    have tie := circular_midpoint_is_boundary sites θ increasing bounds chart.origin radius_positive
      position first last at_first at_last two m.property hr.1
    have actual := (chart.cut_diagram _ (inside m)).mpr tie
    exact ⟨⟨_, chart.on_surface (inside m)⟩, Or.inl actual, rfl⟩
  let point (m : circularGapMidpoints θ first last) :
      K.circleTrace (u := ⟨b, vertex⟩) chart.toFlatChart ρ :=
    ⟨chart.origin + ρ • direction m, inside m, circle m, on_cut m⟩
  have injective : Function.Injective point := by
    intro m k equal
    have same : chart.origin + ρ • direction m = chart.origin + ρ • direction k :=
      congrArg Subtype.val equal
    exact Subtype.ext (circular_gap_ray_unique θ increasing bounds first last at_first chart.origin
      m.property k.property hr.1 hr.1 same).1
  have surjective : Function.Surjective point := by
    intro x
    have near := disk (show (x : Plane) ∈ Metric.ball chart.origin ε by
      change dist _ _ < ε
      rw [x.property.2.1]
      exact hr.2)
    have actual : chart.map x ∈ P.multipleRouteLocus a := by
      obtain ⟨c, cut, mapped⟩ := x.property.2.2
      rcases cut with multiple | original
      · rwa [mapped] at multiple
      · exact (near.2 (mapped ▸ original.1)).elim
    rcases (chart.cut_iff_gap_ray different sites θ increasing bounds position
      first last at_first at_last two x x.property.1).mp actual with center | ⟨σ, sp, m, hm, representation⟩
    · have distance := x.property.2.1
      rw [center, dist_self] at distance
      linarith [hr.1]
    · have radii : σ = ρ := by
        have distance := x.property.2.1
        rw [representation, dist_eq_norm, add_sub_cancel_left, norm_smul, direction_norm,
          mul_one, Real.norm_eq_abs, abs_of_pos sp] at distance
        exact distance
      refine ⟨⟨m, hm⟩, Subtype.ext ?_⟩
      change chart.origin + ρ • direction m = (x : Plane)
      simpa only [radii] using representation.symm
  exact ⟨Equiv.ofBijective point ⟨injective, surjective⟩, fun _ => rfl⟩

/-- The local cut-ray order is in bijection with the actual incident edges,
with the matching point proved to lie strictly inside the matched edge. -/
theorem midpoints_equiv_neighbors (K : P.EmbeddedCutGraph a) (vertex : (b : Space) ∈ K.vertices)
    (different : a ≠ b) (not_vertex : (b : Space) ∉ P.vertices)
    (sites : Fin chart.sources.ncard ≃ chart.sources) (θ : Fin chart.sources.ncard → ℝ)
    (increasing : StrictMono θ) (bounds : ∀ i, 0 ≤ θ i ∧ θ i < 2 * π)
    (position : ∀ i, (sites i : Plane) = chart.origin + P.surfaceDist a b • direction (θ i))
    (first last : Fin chart.sources.ncard) (at_first : first.val = 0)
    (at_last : last.val + 1 = chart.sources.ncard) (two : first < last) :
    ∃ ε > 0, ∀ ρ ∈ Ioo (0 : ℝ) ε,
      ∃ e : circularGapMidpoints θ first last ≃ {v : K.vertices // K.graph.Adj ⟨b, vertex⟩ v},
        ∀ m, chart.map (chart.origin + ρ • direction m) ∈
          openSegment ℝ (b : Space) ((e m).val : Space) := by
  obtain ⟨δ, dp, rays⟩ := chart.midpoints_equiv_circle K vertex different not_vertex
    sites θ increasing bounds position first last at_first at_last two
  obtain ⟨η, ep, edges⟩ := K.neighbors_equiv_circle ⟨b, vertex⟩ chart.toFlatChart
  refine ⟨min δ η, lt_min dp ep, ?_⟩
  intro ρ hr
  obtain ⟨ray, at_ray⟩ := rays ρ ⟨hr.1, hr.2.trans_le (min_le_left _ _)⟩
  obtain ⟨edge, on_edge⟩ := edges ρ ⟨hr.1, hr.2.trans_le (min_le_right _ _)⟩
  refine ⟨ray.trans edge.symm, ?_⟩
  intro m
  have location := on_edge (edge.symm (ray m))
  rw [edge.apply_symm_apply, at_ray m] at location
  exact location

/-- One edge label works along the whole short positive ray. The bijection
is independent of the radius used to identify the incident edges. -/
theorem gap_rays_equiv_neighbors (K : P.EmbeddedCutGraph a) (vertex : (b : Space) ∈ K.vertices)
    (different : a ≠ b) (not_vertex : (b : Space) ∉ P.vertices)
    (sites : Fin chart.sources.ncard ≃ chart.sources) (θ : Fin chart.sources.ncard → ℝ)
    (increasing : StrictMono θ) (bounds : ∀ i, 0 ≤ θ i ∧ θ i < 2 * π)
    (position : ∀ i, (sites i : Plane) = chart.origin + P.surfaceDist a b • direction (θ i))
    (first last : Fin chart.sources.ncard) (at_first : first.val = 0)
    (at_last : last.val + 1 = chart.sources.ncard) (two : first < last) :
    ∃ ε > 0, ∃ e : circularGapMidpoints θ first last ≃ {v : K.vertices // K.graph.Adj ⟨b, vertex⟩ v},
      ∀ m, ∀ ρ ∈ Ioo (0 : ℝ) ε, chart.map (chart.origin + ρ • direction m) ∈
        openSegment ℝ (b : Space) ((e m).val : Space) := by
  obtain ⟨δ, dp, match_at_radius⟩ := chart.midpoints_equiv_neighbors K vertex different not_vertex
    sites θ increasing bounds position first last at_first at_last two
  have open_avoid : IsOpen (K.vertices \ {(b : Space)})ᶜ :=
    (K.finite_vertices.subset diff_subset).isClosed.isOpen_compl
  have center : chart.origin ∈ chart.domain ∩ chart.map ⁻¹' (K.vertices \ {(b : Space)})ᶜ :=
    ⟨chart.origin_mem, by
      change chart.map chart.origin ∉ K.vertices \ {(b : Space)}
      rw [chart.at_origin]
      exact fun h => h.2 rfl⟩
  obtain ⟨η, ep, disk⟩ := Metric.isOpen_iff.mp
    (chart.open_domain.inter (open_avoid.preimage chart.continuous)) chart.origin center
  let ε := min δ η
  have positive : 0 < ε := lt_min dp ep
  have sample_in : ε / 2 ∈ Ioo (0 : ℝ) ε := ⟨half_pos positive, half_lt_self positive⟩
  obtain ⟨e, located⟩ := match_at_radius (ε / 2) ⟨sample_in.1, sample_in.2.trans_le (min_le_left _ _)⟩
  have circle (m : ℝ) {ρ : ℝ} (rp : 0 < ρ) :
      dist (chart.origin + ρ • direction m) chart.origin = ρ := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, direction_norm, mul_one,
      Real.norm_eq_abs, abs_of_pos rp]
  have near (m : ℝ) {ρ : ℝ} (hr : ρ ∈ Ioo (0 : ℝ) ε) :
      chart.origin + ρ • direction m ∈ chart.domain ∩ chart.map ⁻¹' (K.vertices \ {(b : Space)})ᶜ :=
    disk (show chart.origin + ρ • direction m ∈ Metric.ball chart.origin η by
      change dist _ _ < η
      rw [circle m hr.1]
      exact hr.2.trans_le (min_le_right _ _))
  have no_vertices (m : ℝ) {ρ : ℝ} (hr : ρ ∈ Ioo (0 : ℝ) ε) :
      chart.map (chart.origin + ρ • direction m) ∉ K.vertices := by
    intro is_vertex
    have same : chart.map (chart.origin + ρ • direction m) = (b : Space) := by
      by_contra other
      exact (near m hr).2 ⟨is_vertex, other⟩
    have at_origin := chart.toFlatChart.injective (near m hr).1 chart.origin_mem
      (same.trans chart.at_origin.symm)
    have radius := circle m hr.1
    rw [at_origin, dist_self] at radius
    linarith [hr.1]
  refine ⟨ε, positive, e, ?_⟩
  intro m
  let S := (fun ρ : ℝ => chart.map (chart.origin + ρ • direction m)) '' Ioo (0 : ℝ) ε
  have continuous : Continuous (fun ρ : ℝ => chart.map (chart.origin + ρ • direction m)) :=
    chart.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))
  have connected : IsPreconnected S := isPreconnected_Ioo.image _ continuous.continuousOn
  have on_trace : S ⊆ P.cutSetInSpace a := by
    rintro x ⟨ρ, hr, rfl⟩
    have inside := (near m hr).1
    have multiple := (chart.cut_iff_gap_ray different sites θ increasing bounds position
      first last at_first at_last two _ inside).mpr (Or.inr ⟨ρ, hr.1, m, m.property, rfl⟩)
    exact ⟨⟨_, chart.on_surface inside⟩, Or.inl multiple, rfl⟩
  have avoids : Disjoint S K.vertices := by
    apply disjoint_left.mpr
    rintro x ⟨ρ, hr, rfl⟩
    exact no_vertices m hr
  have meets : (S ∩ openSegment ℝ (b : Space) ((e m).val : Space)).Nonempty :=
    ⟨chart.map (chart.origin + (ε / 2) • direction m), ⟨ε / 2, sample_in, rfl⟩, located m⟩
  have in_edge := K.preconnected_in_one_open_edge connected on_trace avoids (e m).property meets
  intro ρ hr
  exact in_edge ⟨ρ, hr, rfl⟩

end SixVertexUnfolding.ConvexPolyhedron.CutVoronoiChart
