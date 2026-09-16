import SixVertexUnfolding.Geometry.CutVoronoiCharts
import SixVertexUnfolding.Geometry.VoronoiCircleBranches
import SixVertexUnfolding.Geometry.CutArcNotLeaf

/-! A junction chart has at least two distinct cut points on each small
metric circle, which prevents the cut locus from ending on a single edge. -/

namespace SixVertexUnfolding.ConvexPolyhedron.CutVoronoiChart

open Set

variable {P : ConvexPolyhedron} {a b : frontier P.body} (chart : P.CutVoronoiChart a b)

include chart in
/-- A target with at least three routes cannot have a one-sided cofacial cut neighborhood. -/
theorem junction_not_one_sided (different : a ≠ b) (many : 2 < Nat.card (P.geodesicFiber a b))
    (c : Space) (F : P.Face) (cofacial : segment ℝ (b : Space) c ⊆ F.val)
    (U : Set Space) (openU : IsOpen U) (bU : (b : Space) ∈ U)
    (one_sided : ∀ x ∈ chart.domain, chart.map x ∈ U →
      chart.map x ∈ P.multipleRouteLocus a → chart.map x ∈ segment ℝ (b : Space) c) : False := by
  have positive : 0 < P.surfaceDist a b := by
    apply lt_of_le_of_ne (P.surfaceDist_nonneg a b)
    intro zero
    exact different (Subtype.ext ((P.surfaceDist_eq_zero_iff a.property b.property).mp zero.symm))
  let D := chart.domain ∩ chart.map ⁻¹' U
  have openD : IsOpen D := chart.open_domain.inter (openU.preimage chart.continuous)
  have center : chart.origin ∈ D := ⟨chart.origin_mem, by change chart.map chart.origin ∈ U; rwa [chart.at_origin]⟩
  obtain ⟨ε, epsilon_positive, disk⟩ := Metric.isOpen_iff.mp openD chart.origin center
  let ρ := min ε (P.surfaceDist a b) / 2
  have radius_positive : 0 < ρ := half_pos (lt_min epsilon_positive positive)
  have radius_small : ρ ≤ P.surfaceDist a b := by
    have := min_le_right ε (P.surfaceDist a b)
    dsimp [ρ]
    linarith
  have radius_epsilon : ρ < ε := by
    have := min_le_left ε (P.surfaceDist a b)
    dsimp [ρ]
    linarith
  have circle_in (x : Plane) (hx : x ∈ Metric.sphere chart.origin ρ) : x ∈ D :=
    disk (by change dist x chart.origin < ε; rw [hx]; exact radius_epsilon)
  have branches := voronoi_circle_not_subsingleton chart.sources chart.finite_sources
    chart.origin (P.surfaceDist a b) ρ positive radius_positive radius_small chart.source_distance
    (by rw [chart.route_count]; exact many)
  obtain ⟨x, hx, y, hy, distinct⟩ := not_subsingleton_iff.mp branches
  have xD := circle_in x hx.1
  have yD := circle_in y hy.1
  have forward := one_sided x xD.1 xD.2 ((chart.cut_diagram x xD.1).mpr hx.2)
  have backward := one_sided y yD.1 yD.2 ((chart.cut_diagram y yD.1).mpr hy.2)
  have bF : (b : Space) ∈ F.val := cofacial (left_mem_segment ℝ _ _)
  have equal_distance : dist (b : Space) (chart.map x) = dist (b : Space) (chart.map y) := by
    rw [← P.surfaceDist_eq_dist_in_face F bF (cofacial forward),
      ← P.surfaceDist_eq_dist_in_face F bF (cofacial backward)]
    have first := chart.distance chart.origin chart.origin_mem x xD.1
    have second := chart.distance chart.origin chart.origin_mem y yD.1
    simp only [chart.at_origin] at first second
    rw [first, second, dist_comm chart.origin x, dist_comm chart.origin y, hx.1, hy.1]
  have same := space_segment_point_unique (b : Space) c _ _ forward backward equal_distance
  apply distinct
  apply dist_eq_zero.mp
  rw [← chart.distance x xD.1 y yD.1, same, P.surfaceDist_self (chart.on_surface yD.1)]

end SixVertexUnfolding.ConvexPolyhedron.CutVoronoiChart
