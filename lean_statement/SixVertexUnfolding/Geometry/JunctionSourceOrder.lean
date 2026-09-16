import SixVertexUnfolding.Geometry.CutVoronoiRoutes
import SixVertexUnfolding.Geometry.CircularVoronoiRays

/-! The circular order of a nonvertex junction's actual shortest routes.
The gap rays describe the entire local multiple-route locus, including the
closing gap. Their identification with incident tree edges and the global
source-angle sum remain separate from these local conclusions.
-/

namespace SixVertexUnfolding.ConvexPolyhedron.CutVoronoiChart

open Real Set

variable {P : ConvexPolyhedron} {a b : frontier P.body} (chart : P.CutVoronoiChart a b)

private theorem source_radius_positive (different : a ≠ b) : 0 < P.surfaceDist a b := by
  apply lt_of_le_of_ne (P.surfaceDist_nonneg a b)
  intro zero
  exact different (Subtype.ext ((P.surfaceDist_eq_zero_iff a.property b.property).mp zero.symm))

/-- The angular enumeration is an enumeration of actual route tails,
all read simultaneously in the same chart. -/
theorem ordered_route_tails (different : a ≠ b)
    (finite_routes : (P.geodesicFiber a b).Finite) :
    ∃ sites : Fin chart.sources.ncard ≃ chart.sources,
      ∃ θ : Fin chart.sources.ncard → ℝ,
      ∃ routes : Fin chart.sources.ncard ≃ P.geodesicFiber a b,
      ∃ start : unitInterval, start < 1 ∧ StrictMono θ ∧
        (∀ i, 0 ≤ θ i ∧ θ i < 2 * π) ∧
        (∀ i, (sites i : Plane) = chart.origin + P.surfaceDist a b • direction (θ i)) ∧
        ∀ i, ∀ t ∈ Icc start 1,
          chart.origin + ((1 - (t : ℝ)) * P.surfaceDist a b) • direction (θ i) ∈ chart.domain ∧
          chart.map (chart.origin + ((1 - (t : ℝ)) * P.surfaceDist a b) • direction (θ i)) =
            ((routes i).val t : Space) := by
  obtain ⟨sites, θ, increasing, bounds, position⟩ := exists_circular_source_order
    chart.sources chart.finite_sources chart.origin (P.surfaceDist a b)
    (source_radius_positive different) chart.source_distance
  obtain ⟨e, start, before, tails⟩ := chart.uniform_route_tails finite_routes
  refine ⟨sites, θ, sites.trans e, start, before, increasing, bounds, position, ?_⟩
  intro i t ht
  have line : AffineMap.lineMap (sites i : Plane) chart.origin (t : ℝ) =
      chart.origin + ((1 - (t : ℝ)) * P.surfaceDist a b) • direction (θ i) := by
    rw [position i, AffineMap.lineMap_apply_module]
    module
  simpa only [line] using tails (sites i) t ht

/-- Any empty circular gap supplies an actual local cut ray on the surface. -/
theorem gap_cut_ray (different : a ≠ b) {α β : ℝ}
    (ordered : α < β) (one_turn : β < α + 2 * π)
    (first : chart.origin + P.surfaceDist a b • direction α ∈ chart.sources)
    (second : chart.origin + P.surfaceDist a b • direction β ∈ chart.sources)
    (empty_gap : ∀ p ∈ chart.sources, ∃ φ ∈ Icc β (α + 2 * π),
      p = chart.origin + P.surfaceDist a b • direction φ) :
    ∃ ε > 0, ∀ ρ ∈ Ioo (0 : ℝ) ε,
      let x := chart.origin + ρ • direction ((α + β) / 2)
      x ∈ chart.domain ∧ chart.map x ∈ P.multipleRouteLocus a ∧
        x ∈ voronoiRidge chart.sources
          (chart.origin + P.surfaceDist a b • direction α)
          (chart.origin + P.surfaceDist a b • direction β) ∧
        ∀ s ∈ chart.sources,
          s ≠ chart.origin + P.surfaceDist a b • direction α →
          s ≠ chart.origin + P.surfaceDist a b • direction β →
          dist (chart.origin + P.surfaceDist a b • direction α) x < dist s x := by
  obtain ⟨ε, positive, disk⟩ := Metric.isOpen_iff.mp chart.open_domain chart.origin chart.origin_mem
  refine ⟨ε, positive, ?_⟩
  intro ρ hr
  have radius : dist (chart.origin + ρ • direction ((α + β) / 2)) chart.origin = ρ := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, direction_norm, mul_one,
      Real.norm_eq_abs, abs_of_pos hr.1]
  have inside := disk (show chart.origin + ρ • direction ((α + β) / 2) ∈ Metric.ball chart.origin ε by
    change dist _ _ < ε
    rw [radius]
    exact hr.2)
  have ray := circular_gap_voronoi_ray chart.sources chart.origin
    (source_radius_positive different) hr.1 ordered one_turn first second empty_gap
  exact ⟨inside, (chart.cut_diagram _ inside).mpr ray.2.1, ray.2.2.1, ray.2.2.2⟩

/-- Consecutive entries in the source order produce their bisecting cut ray. -/
theorem consecutive_cut_ray (different : a ≠ b)
    (sites : Fin chart.sources.ncard ≃ chart.sources) (θ : Fin chart.sources.ncard → ℝ)
    (increasing : StrictMono θ) (bounds : ∀ i, 0 ≤ θ i ∧ θ i < 2 * π)
    (position : ∀ i, (sites i : Plane) = chart.origin + P.surfaceDist a b • direction (θ i))
    (i j : Fin chart.sources.ncard) (next : j.val = i.val + 1) :
    ∃ ε > 0, ∀ ρ ∈ Ioo (0 : ℝ) ε,
      chart.map (chart.origin + ρ • direction ((θ i + θ j) / 2)) ∈ P.multipleRouteLocus a := by
  have gap := circular_order_gap sites θ increasing bounds chart.origin (P.surfaceDist a b) position i j next
  obtain ⟨ε, positive, ray⟩ := chart.gap_cut_ray different (increasing (by omega))
    (show θ j < θ i + 2 * π by linarith [(bounds i).1, (bounds j).2])
    (position i ▸ (sites i).property) (position j ▸ (sites j).property) gap
  exact ⟨ε, positive, fun ρ hr => (ray ρ hr).2.1⟩

/-- The last-to-first gap supplies the remaining cut ray across the end of the list. -/
theorem closing_cut_ray (different : a ≠ b)
    (sites : Fin chart.sources.ncard ≃ chart.sources) (θ : Fin chart.sources.ncard → ℝ)
    (increasing : StrictMono θ) (bounds : ∀ i, 0 ≤ θ i ∧ θ i < 2 * π)
    (position : ∀ i, (sites i : Plane) = chart.origin + P.surfaceDist a b • direction (θ i))
    (first last : Fin chart.sources.ncard) (at_first : first.val = 0)
    (at_last : last.val + 1 = chart.sources.ncard) (two : first < last) :
    ∃ ε > 0, ∀ ρ ∈ Ioo (0 : ℝ) ε,
      chart.map (chart.origin + ρ • direction ((θ last + (θ first + 2 * π)) / 2)) ∈
        P.multipleRouteLocus a := by
  have gap := closing_circular_order_gap sites θ increasing chart.origin (P.surfaceDist a b)
    position first last at_first at_last
  have first_mem : chart.origin + P.surfaceDist a b • direction (θ first + 2 * π) ∈ chart.sources := by
    rw [direction_add_two_pi]
    exact position first ▸ (sites first).property
  obtain ⟨ε, positive, ray⟩ := chart.gap_cut_ray different
    (show θ last < θ first + 2 * π by linarith [(bounds first).1, (bounds last).2])
    (show θ first + 2 * π < θ last + 2 * π by linarith [increasing two])
    (position last ▸ (sites last).property) first_mem gap
  exact ⟨ε, positive, fun ρ hr => (ray ρ hr).2.1⟩

/-- The actual multiple-route locus in the chart is exactly the junction and
its listed gap rays; no extra local cut branch is possible. -/
theorem cut_iff_gap_ray (different : a ≠ b)
    (sites : Fin chart.sources.ncard ≃ chart.sources) (θ : Fin chart.sources.ncard → ℝ)
    (increasing : StrictMono θ) (bounds : ∀ i, 0 ≤ θ i ∧ θ i < 2 * π)
    (position : ∀ i, (sites i : Plane) = chart.origin + P.surfaceDist a b • direction (θ i))
    (first last : Fin chart.sources.ncard) (at_first : first.val = 0)
    (at_last : last.val + 1 = chart.sources.ncard) (two : first < last)
    (x : Plane) (inside : x ∈ chart.domain) :
    chart.map x ∈ P.multipleRouteLocus a ↔ x = chart.origin ∨
      ∃ (ρ : ℝ), 0 < ρ ∧ ∃ m ∈ circularGapMidpoints θ first last,
        x = chart.origin + ρ • direction m :=
  (chart.cut_diagram x inside).trans (circular_voronoi_boundary_iff sites θ increasing bounds
    chart.origin (source_radius_positive different) position first last at_first at_last two x)

end SixVertexUnfolding.ConvexPolyhedron.CutVoronoiChart
