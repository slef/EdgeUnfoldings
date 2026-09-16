import SixVertexUnfolding.Geometry.CutVoronoiRoutes
import SixVertexUnfolding.Geometry.CircularVoronoiSectors

/-! In a junction chart, nearest source copies give actual surface distances.
The same copy controls the distance of nearby routes in a continuous branch.
-/

namespace SixVertexUnfolding.ConvexPolyhedron.CutVoronoiChart

open Real Set Filter
open scoped Topology

variable {P : ConvexPolyhedron} {a b : frontier P.body} (chart : P.CutVoronoiChart a b)

/-- A nearest chart source attains the actual intrinsic distance. -/
theorem distance_of_nearest {x p : Plane} (inside : x ∈ chart.domain)
    (member : p ∈ chart.sources) (nearest : ∀ q ∈ chart.sources, dist p x ≤ dist q x) :
    P.surfaceDist a (chart.map x) = dist p x := by
  obtain ⟨lower, q, hq, attained⟩ := chart.local_distance x inside
  exact le_antisymm (lower p member) (attained ▸ nearest q hq)

/-- At a positive gap-ray point, only the two endpoint sources attain the
actual shortest-path distance. -/
theorem gap_distance_iff (different : a ≠ b) {α β ρ : ℝ}
    (ordered : α < β) (one_turn : β < α + 2 * π) (positive : 0 < ρ)
    (first : chart.origin + P.surfaceDist a b • direction α ∈ chart.sources)
    (second : chart.origin + P.surfaceDist a b • direction β ∈ chart.sources)
    (empty_gap : ∀ p ∈ chart.sources, ∃ φ ∈ Icc β (α + 2 * π),
      p = chart.origin + P.surfaceDist a b • direction φ)
    (inside : chart.origin + ρ • direction ((α + β) / 2) ∈ chart.domain)
    {p : Plane} (member : p ∈ chart.sources) :
    P.surfaceDist a (chart.map (chart.origin + ρ • direction ((α + β) / 2))) =
      dist p (chart.origin + ρ • direction ((α + β) / 2)) ↔
        p = chart.origin + P.surfaceDist a b • direction α ∨
        p = chart.origin + P.surfaceDist a b • direction β := by
  have radius_positive : 0 < P.surfaceDist a b := by
    simpa using tail_radius_pos different (0 : unitInterval) (by change (0 : ℝ) < 1; norm_num)
  have ray := circular_gap_voronoi_ray chart.sources chart.origin radius_positive positive
    ordered one_turn first second empty_gap
  have actual := chart.distance_of_nearest inside first ray.2.2.1.2
  constructor
  · intro attained
    by_contra neither
    push Not at neither
    have strict := ray.2.2.2 p member neither.1 neither.2
    exact (ne_of_lt strict) (actual.symm.trans attained)
  · rintro (rfl | rfl)
    · exact actual
    · exact actual.trans ray.2.2.1.1

/-- Continuity of an actual route family preserves its source-distance
formula near a represented route. The endpoint may move within the chart. -/
theorem Represents.family_distance {ι : Type*} [TopologicalSpace ι]
    {routes : ι → P.BoundaryCurve} {i : ι} {p : Plane}
    (represented : chart.Represents p (routes i))
    (member : routes i ∈ P.geodesicFiber a b) (continuous : ContinuousAt routes i) :
    ∀ᶠ j in 𝓝 i, routes j ∈ P.geodesicCurves → routes j 0 = a →
      ∀ x ∈ chart.domain, chart.map x = (routes j 1 : Space) →
        P.surfaceDist a (chart.map x) = dist p x := by
  obtain ⟨W, openW, original, formula⟩ := chart.route_stability p (routes i) member represented
  filter_upwards [continuous.eventually (openW.mem_nhds original)] with j hj
  exact formula (routes j) hj

end SixVertexUnfolding.ConvexPolyhedron.CutVoronoiChart
