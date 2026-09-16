import SixVertexUnfolding.Geometry.CutVoronoiCharts
import SixVertexUnfolding.Geometry.FlatChartCoordinates

/-! A junction's planar source copies label the actual shortest routes.
All route tails can be read simultaneously in one chart, on concentric
circles. This retains the geometry needed when ordering the incident sectors.
-/

namespace SixVertexUnfolding.ConvexPolyhedron.CutVoronoiChart

open Set

variable {P : ConvexPolyhedron} {a b : frontier P.body} (chart : P.CutVoronoiChart a b)

/-- A source copy represents the actual final straight part of this route. -/
def Represents (p : Plane) (f : P.BoundaryCurve) : Prop :=
  ∃ start : unitInterval, start < 1 ∧ ∀ t ∈ Icc start 1,
    AffineMap.lineMap p chart.origin (t : ℝ) ∈ chart.domain ∧
    chart.map (AffineMap.lineMap p chart.origin (t : ℝ)) = (f t : Space)

/-- One route cannot have two distinct source copies in the same chart. -/
theorem represented_source_unique {p q : Plane} {f : P.BoundaryCurve}
    (first : chart.Represents p f) (second : chart.Represents q f) : p = q := by
  obtain ⟨s, sb, first⟩ := first
  obtain ⟨u, ub, second⟩ := second
  obtain ⟨t, after, before⟩ := exists_between (max_lt sb ub)
  have left := first t ⟨(le_max_left s u).trans after.le, before.le⟩
  have right := second t ⟨(le_max_right s u).trans after.le, before.le⟩
  exact lineMap_left_unique p q chart.origin (t : ℝ) (show (t : ℝ) < 1 from before).ne
    (chart.toFlatChart.injective left.1 right.1 (left.2.trans right.2.symm))

/-- The source/route bijection preserves the actual terminal coordinate formula. -/
theorem sources_equiv_routes (finite_routes : (P.geodesicFiber a b).Finite) :
    ∃ e : chart.sources ≃ P.geodesicFiber a b,
      ∀ p : chart.sources, chart.Represents (p : Plane) (e p) := by
  classical
  letI := finite_routes.fintype
  have exists_route (p : chart.sources) :
      ∃ f : P.geodesicFiber a b, chart.Represents p f := by
    obtain ⟨f, hf, tail⟩ := (chart.source_routes p).mp p.property
    exact ⟨⟨f, hf⟩, tail⟩
  choose route represents using exists_route
  have injective : Function.Injective route := by
    intro p q equal
    apply Subtype.ext
    exact chart.represented_source_unique (represents p) (equal.symm ▸ represents q)
  have bijective := (Nat.bijective_iff_injective_and_card route).mpr
    ⟨injective, chart.route_count⟩
  exact ⟨Equiv.ofBijective route bijective, represents⟩

/-- Every actual route has the source selected by the inverse bijection. -/
theorem route_has_source (finite_routes : (P.geodesicFiber a b).Finite)
    (f : P.geodesicFiber a b) : ∃ p ∈ chart.sources, chart.Represents p f := by
  obtain ⟨e, represents⟩ := chart.sources_equiv_routes finite_routes
  exact ⟨e.symm f, (e.symm f).property, by simpa using represents (e.symm f)⟩

/-- Equal source labels identify actual routes, using the proved source/route bijection. -/
theorem represented_routes_agree (finite_routes : (P.geodesicFiber a b).Finite)
    {f g : P.BoundaryCurve} (hf : f ∈ P.geodesicFiber a b) (hg : g ∈ P.geodesicFiber a b)
    {p : Plane} (first : chart.Represents p f) (second : chart.Represents p g) : f = g := by
  obtain ⟨e, represents⟩ := chart.sources_equiv_routes finite_routes
  let F : P.geodesicFiber a b := ⟨f, hf⟩
  let G : P.geodesicFiber a b := ⟨g, hg⟩
  have first_label : (e.symm F : Plane) = p := chart.represented_source_unique
    (by simpa only [e.apply_symm_apply] using represents (e.symm F)) first
  have second_label : (e.symm G : Plane) = p := chart.represented_source_unique
    (by simpa only [e.apply_symm_apply] using represents (e.symm G)) second
  exact congrArg Subtype.val (e.symm.injective (Subtype.ext (first_label.trans second_label.symm)))

/-- All source copies and all routes share one terminal parameter interval. -/
theorem uniform_route_tails (finite_routes : (P.geodesicFiber a b).Finite) :
    ∃ e : chart.sources ≃ P.geodesicFiber a b,
      ∃ start : unitInterval, start < 1 ∧ ∀ p : chart.sources, ∀ t ∈ Icc start 1,
        AffineMap.lineMap (p : Plane) chart.origin (t : ℝ) ∈ chart.domain ∧
        chart.map (AffineMap.lineMap (p : Plane) chart.origin (t : ℝ)) = ((e p).val t : Space) := by
  classical
  letI := chart.finite_sources.fintype
  obtain ⟨e, represents⟩ := chart.sources_equiv_routes finite_routes
  choose start before tail using represents
  let s := Finset.univ.sup start
  refine ⟨e, s, (Finset.sup_lt_iff (show (⊥ : unitInterval) < 1 by change (0 : ℝ) < 1; norm_num)).mpr
    (fun p _ => before p), ?_⟩
  intro p t ht
  exact tail p t ⟨(Finset.le_sup (Finset.mem_univ p)).trans ht.1, ht.2⟩

/-- A common tail parameter samples every represented route on one planar circle. -/
theorem tail_radius (p : chart.sources) (t : unitInterval) :
    dist (AffineMap.lineMap (p : Plane) chart.origin (t : ℝ)) chart.origin =
      (1 - (t : ℝ)) * P.surfaceDist a b := by
  rw [dist_lineMap_right, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr t.property.2),
    chart.source_distance p p.property]

/-- Before the junction, different source copies give different points in the chart. -/
theorem distinct_tail_points {p q : chart.sources} (different : p ≠ q)
    (t : unitInterval) (before : t < 1) :
    AffineMap.lineMap (p : Plane) chart.origin (t : ℝ) ≠
      AffineMap.lineMap (q : Plane) chart.origin (t : ℝ) := by
  intro equal
  exact different (Subtype.ext (lineMap_left_unique _ _ _ (t : ℝ)
    (show (t : ℝ) < 1 from before).ne equal))

/-- The common circle radius is positive whenever the source and junction differ. -/
theorem tail_radius_pos (different : a ≠ b) (t : unitInterval) (before : t < 1) :
    0 < (1 - (t : ℝ)) * P.surfaceDist a b := by
  apply mul_pos (sub_pos.mpr (show (t : ℝ) < 1 from before))
  apply lt_of_le_of_ne (P.surfaceDist_nonneg a b)
  intro zero
  exact different (Subtype.ext ((P.surfaceDist_eq_zero_iff a.property b.property).mp zero.symm))

end SixVertexUnfolding.ConvexPolyhedron.CutVoronoiChart

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- At every nonsource nonvertex junction, one genuine flat chart simultaneously
represents every shortest route by its corresponding planar source copy. -/
theorem cut_voronoi_chart_with_routes (a b : frontier P.body) (different : a ≠ b)
    (not_vertex : (b : Space) ∉ P.vertices) :
    ∃ chart : P.CutVoronoiChart a b, ∃ e : chart.sources ≃ P.geodesicFiber a b,
      ∃ start : unitInterval, start < 1 ∧ ∀ p : chart.sources, ∀ t ∈ Icc start 1,
        AffineMap.lineMap (p : Plane) chart.origin (t : ℝ) ∈ chart.domain ∧
        chart.map (AffineMap.lineMap (p : Plane) chart.origin (t : ℝ)) = ((e p).val t : Space) := by
  obtain ⟨chart⟩ := graph.cut_voronoi_chart small_faces a b different not_vertex
  exact ⟨chart, chart.uniform_route_tails (graph.geodesicFiber_finite small_faces a b different)⟩

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
