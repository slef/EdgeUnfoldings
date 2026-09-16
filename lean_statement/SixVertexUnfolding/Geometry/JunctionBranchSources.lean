import SixVertexUnfolding.Geometry.CutVoronoiDistances
import SixVertexUnfolding.Geometry.JunctionIncidence
import SixVertexUnfolding.Geometry.ClosedCutEdgeRoutes
import SixVertexUnfolding.Geometry.RouteBranchSeparation

/-! The limiting source of a continuous branch on an incident cut edge
is one of the two sources bounding that edge's angular gap.
-/

namespace SixVertexUnfolding.ConvexPolyhedron

open Real Set

namespace FlatChart

variable {P : ConvexPolyhedron} {b : Space} (chart : P.FlatChart b)

/-- On a cofacial segment starting at the chart center, the planar radius
is the ordinary fraction of the full edge length. -/
theorem ray_segment_parameter (v : Space) (F : P.Face)
    (cofacial : segment ℝ b v ⊆ F.val) {x : Plane} (inside : x ∈ chart.domain)
    {t : ℝ} (between : t ∈ Icc (0 : ℝ) 1)
    (on_edge : chart.map x ∈ segment ℝ b v)
    (radius : dist x chart.origin = t * dist b v) :
    chart.map x = AffineMap.lineMap b v t := by
  have actual := chart.distance chart.origin chart.origin_mem x inside
  rw [chart.at_origin, P.surfaceDist_eq_dist_in_face F
    (cofacial (left_mem_segment ℝ _ _)) (cofacial on_edge), dist_comm chart.origin x,
    radius] at actual
  have candidate : dist b (AffineMap.lineMap b v t) = t * dist b v := by
    rw [dist_left_lineMap, Real.norm_eq_abs, abs_of_nonneg between.1]
  have in_segment : AffineMap.lineMap b v t ∈ segment ℝ b v := by
    rw [segment_eq_image_lineMap]
    exact ⟨t, between, rfl⟩
  exact space_segment_point_unique b v (chart.map x) (AffineMap.lineMap b v t)
    on_edge in_segment (actual.trans candidate.symm)

end FlatChart

namespace CutVoronoiChart

variable {P : ConvexPolyhedron} {a b : frontier P.body} (chart : P.CutVoronoiChart a b)

/-- A sufficiently short positive edge parameter samples the assigned ray
inside the chart. The parameter can also be made smaller than any given bound. -/
theorem incident_edge_sample (T : P.CutLocusTree a)
    {u v : T.vertices} (edge : T.graph.Adj u v) (at_junction : T.vertexTarget u = b)
    {m ε δ : ℝ} (positive : 0 < ε) (delta_positive : 0 < δ)
    (on_ray : ∀ ρ ∈ Ioo (0 : ℝ) ε,
      chart.map (chart.origin + ρ • direction m) ∈ openSegment ℝ (b : Space) (v : Space)) :
    ∃ t : unitInterval, 0 < t ∧ t < 1 ∧ (t : ℝ) < δ ∧
      (t : ℝ) * dist (b : Space) (v : Space) < ε ∧
      let x := chart.origin + ((t : ℝ) * dist (b : Space) (v : Space)) • direction m
      x ∈ chart.domain ∧ chart.map x = (T.closedEdgeTarget edge t : Space) := by
  have u_eq : (u : Space) = (b : Space) := congrArg Subtype.val at_junction
  have length_positive : 0 < dist (b : Space) (v : Space) := by
    apply dist_pos.mpr
    intro same
    exact edge.ne (Subtype.ext (u_eq.trans same))
  obtain ⟨F, cofacial⟩ := T.toEmbeddedCutGraph.cofacial_edges u v edge
  rw [u_eq] at cofacial
  obtain ⟨η, ep, disk⟩ := Metric.isOpen_iff.mp chart.open_domain chart.origin chart.origin_mem
  obtain ⟨s, sp, short⟩ := exists_between (lt_min (show (0 : ℝ) < 1 by norm_num)
    (lt_min delta_positive (div_pos (lt_min positive ep) length_positive)))
  let t : unitInterval := ⟨s, sp.le, (short.trans_le (min_le_left _ _)).le⟩
  have t_small : s < δ := short.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have radius_small : s * dist (b : Space) (v : Space) < min ε η :=
    (lt_div_iff₀ length_positive).mp
      (short.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  let ρ := s * dist (b : Space) (v : Space)
  have rp : 0 < ρ := mul_pos sp length_positive
  let x := chart.origin + ρ • direction m
  have radius : dist x chart.origin = ρ := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, direction_norm, mul_one,
      Real.norm_eq_abs, abs_of_pos rp]
  have inside : x ∈ chart.domain := disk (show x ∈ Metric.ball chart.origin η by
    change dist x chart.origin < η
    rw [radius]
    exact radius_small.trans_le (min_le_right _ _))
  have on_edge := on_ray ρ ⟨rp, radius_small.trans_le (min_le_left _ _)⟩
  refine ⟨t, sp, short.trans_le (min_le_left _ _), t_small,
    radius_small.trans_le (min_le_left _ _), inside, ?_⟩
  change chart.map x = AffineMap.lineMap (u : Space) (v : Space) (t : ℝ)
  rw [u_eq]
  exact chart.toFlatChart.ray_segment_parameter v F cofacial inside t.property
    (openSegment_subset_segment ℝ _ _ on_edge) radius

/-- A branch extending continuously to this junction must approach through
one of the two source directions adjacent to its incident cut edge. -/
theorem incident_branch_source (T : P.CutLocusTree a)
    {u v : T.vertices} (edge : T.graph.Adj u v) (at_junction : T.vertexTarget u = b)
    (routes : C(unitInterval, P.BoundaryCurve))
    (member : ∀ t, routes t ∈ P.geodesicFiber a (T.closedEdgeTarget edge t))
    {p : Plane} (represented : chart.Represents p (routes 0))
    {α β ε : ℝ} (ordered : α < β) (one_turn : β < α + 2 * π)
    (first : chart.origin + P.surfaceDist a b • direction α ∈ chart.sources)
    (second : chart.origin + P.surfaceDist a b • direction β ∈ chart.sources)
    (empty_gap : ∀ q ∈ chart.sources, ∃ φ ∈ Icc β (α + 2 * π),
      q = chart.origin + P.surfaceDist a b • direction φ)
    (positive : 0 < ε)
    (on_ray : ∀ ρ ∈ Ioo (0 : ℝ) ε,
      chart.map (chart.origin + ρ • direction ((α + β) / 2)) ∈
        openSegment ℝ (b : Space) (v : Space)) :
    p = chart.origin + P.surfaceDist a b • direction α ∨
    p = chart.origin + P.surfaceDist a b • direction β := by
  have start_member : routes 0 ∈ P.geodesicFiber a b := by
    simpa only [T.closedEdgeTarget_zero, at_junction] using member 0
  have source_member : p ∈ chart.sources :=
    (chart.source_routes p).mpr ⟨routes 0, start_member, represented⟩
  have different : a ≠ b := at_junction ▸ T.vertexTarget_different u
  obtain ⟨W, openW, original, formula⟩ := chart.route_stability p (routes 0) start_member represented
  obtain ⟨δ, dp, near_routes⟩ := Metric.isOpen_iff.mp
    (openW.preimage routes.continuous) (0 : unitInterval) original
  obtain ⟨t, tp, _, t_small, _, inside, mapped⟩ :=
    chart.incident_edge_sample T edge at_junction positive dp on_ray
  let ρ := (t : ℝ) * dist (b : Space) (v : Space)
  have length_positive : 0 < dist (b : Space) (v : Space) := by
    apply dist_pos.mpr
    intro same
    exact edge.ne (Subtype.ext ((congrArg Subtype.val at_junction).trans same))
  have rp : 0 < ρ := mul_pos tp length_positive
  let x := chart.origin + ρ • direction ((α + β) / 2)
  have near : routes t ∈ W := near_routes (show t ∈ Metric.ball (0 : unitInterval) δ by
    change dist (t : ℝ) (0 : ℝ) < δ
    simpa only [Real.dist_eq, sub_zero, abs_of_pos (show (0 : ℝ) < t from tp)] using t_small)
  have ends := member t
  have attained := formula (routes t) near ends.1 (congrArg Prod.fst ends.2) x inside
    (mapped.trans (congrArg Subtype.val (congrArg Prod.snd ends.2)).symm)
  exact (chart.gap_distance_iff different ordered one_turn rp first second empty_gap inside
    source_member).mp attained

/-- The two closed branches of an actual edge give exactly its two
adjacent source copies at a nonvertex junction. -/
theorem incident_branch_sources (graph : P.SixVertexGraph)
    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4)
    (T : P.CutLocusTree a) {u v : T.vertices} (edge : T.graph.Adj u v)
    (at_junction : T.vertexTarget u = b) (not_vertex : (b : Space) ∉ P.vertices)
    (S : CutEdgeStrips T edge) (left right : C(unitInterval, P.BoundaryCurve))
    (agrees : ∀ t, left (interiorTime t) = S.first t ∧ right (interiorTime t) = S.second t)
    (member : ∀ t, left t ∈ P.geodesicFiber a (T.closedEdgeTarget edge t) ∧
      right t ∈ P.geodesicFiber a (T.closedEdgeTarget edge t))
    {α β ε : ℝ} (ordered : α < β) (one_turn : β < α + 2 * π)
    (first : chart.origin + P.surfaceDist a b • direction α ∈ chart.sources)
    (second : chart.origin + P.surfaceDist a b • direction β ∈ chart.sources)
    (empty_gap : ∀ q ∈ chart.sources, ∃ φ ∈ Icc β (α + 2 * π),
      q = chart.origin + P.surfaceDist a b • direction φ)
    (positive : 0 < ε)
    (on_ray : ∀ ρ ∈ Ioo (0 : ℝ) ε,
      chart.map (chart.origin + ρ • direction ((α + β) / 2)) ∈
        openSegment ℝ (b : Space) (v : Space)) :
    ∃ p ∈ chart.sources, ∃ q ∈ chart.sources,
      chart.Represents p (left 0) ∧ chart.Represents q (right 0) ∧ p ≠ q ∧
      ({p, q} : Set Plane) =
        {chart.origin + P.surfaceDist a b • direction α,
          chart.origin + P.surfaceDist a b • direction β} := by
  have different : a ≠ b := at_junction ▸ T.vertexTarget_different u
  have endpoints : left 0 ∈ P.geodesicFiber a b ∧ right 0 ∈ P.geodesicFiber a b := by
    simpa only [T.closedEdgeTarget_zero, at_junction] using member 0
  have finite := graph.geodesicFiber_finite small_faces a b different
  obtain ⟨p, hp, represents_left⟩ := chart.route_has_source finite ⟨left 0, endpoints.1⟩
  obtain ⟨q, hq, represents_right⟩ := chart.route_has_source finite ⟨right 0, endpoints.2⟩
  have routes_different : left 0 ≠ right 0 := by
    apply graph.route_branches_distinct_at_zero small_faces a (T.closedEdgeTarget edge) left right
      (fun t => (member t).1) (fun t => (member t).2)
      (by simpa only [T.closedEdgeTarget_zero, at_junction] using different)
      (by simpa only [T.closedEdgeTarget_zero, at_junction] using not_vertex)
    intro t after before same
    let s : Ioo (0 : ℝ) 1 := ⟨t, after, before⟩
    have left_eq : left t = S.first s := (agrees s).1
    have right_eq : right t = S.second s := (agrees s).2
    exact S.distinct s (left_eq.symm.trans (same.trans right_eq))
  have sources_different : p ≠ q := by
    intro same
    exact routes_different (chart.represented_routes_agree finite endpoints.1 endpoints.2
      represents_left (same.symm ▸ represents_right))
  have p_end := chart.incident_branch_source T edge at_junction left (fun t => (member t).1)
    represents_left ordered one_turn first second empty_gap positive on_ray
  have q_end := chart.incident_branch_source T edge at_junction right (fun t => (member t).2)
    represents_right ordered one_turn first second empty_gap positive on_ray
  refine ⟨p, hp, q, hq, represents_left, represents_right, sources_different, ?_⟩
  rcases p_end with p_first | p_second <;> rcases q_end with q_first | q_second
  · exact (sources_different (p_first.trans q_first.symm)).elim
  · rw [p_first, q_second]
  · rw [p_second, q_first, pair_comm]
  · exact (sources_different (p_second.trans q_second.symm)).elim

end CutVoronoiChart
end SixVertexUnfolding.ConvexPolyhedron
