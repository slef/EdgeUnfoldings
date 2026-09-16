import SixVertexUnfolding.Geometry.JunctionBranchSources
import SixVertexUnfolding.Geometry.CutEdgeMetricModel
import SixVertexUnfolding.Geometry.BisectorSourceUniqueness

/-! The metric kite of an incident edge admits a rigid placement in the
junction chart: its base follows the assigned ray and its source copies
are the two actual neighboring sources.
-/

namespace SixVertexUnfolding.ConvexPolyhedron.CutVoronoiChart

open Real Set

variable {P : ConvexPolyhedron} {a b : frontier P.body} (chart : P.CutVoronoiChart a b)

/-- The whole metric kite can be placed in the common junction coordinates,
with the first copy at the first gap source and the second at the second.
This assertion concerns the metric coordinates; agreement of the full
surface triangle maps is a separate obligation. -/
theorem incident_metric_placement (T : P.CutLocusTree a)
    {u v : T.vertices} (edge : T.graph.Adj u v) (at_junction : T.vertexTarget u = b)
    (M : CutEdgeMetricModel T edge)
    {α β ε : ℝ} (ordered : α < β) (one_turn : β < α + 2 * π)
    (first : chart.origin + P.surfaceDist a b • direction α ∈ chart.sources)
    (second : chart.origin + P.surfaceDist a b • direction β ∈ chart.sources)
    (empty_gap : ∀ p ∈ chart.sources, ∃ φ ∈ Icc β (α + 2 * π),
      p = chart.origin + P.surfaceDist a b • direction φ)
    (positive : 0 < ε)
    (on_ray : ∀ ρ ∈ Ioo (0 : ℝ) ε,
      chart.map (chart.origin + ρ • direction ((α + β) / 2)) ∈
        openSegment ℝ (b : Space) (v : Space)) :
    ∃ motion : Plane ≃ᵃⁱ[ℝ] Plane,
      motion M.left = chart.origin ∧
      motion M.right = chart.origin + dist (b : Space) (v : Space) • direction ((α + β) / 2) ∧
      motion M.first = chart.origin + P.surfaceDist a b • direction α ∧
      motion M.second = chart.origin + P.surfaceDist a b • direction β := by
  have different : a ≠ b := at_junction ▸ T.vertexTarget_different u
  have u_eq : (u : Space) = (b : Space) := congrArg Subtype.val at_junction
  let L := dist (b : Space) (v : Space)
  have length_positive : 0 < L := by
    apply dist_pos.mpr
    intro same
    exact edge.ne (Subtype.ext (u_eq.trans same))
  have source_positive : 0 < P.surfaceDist a b := by
    simpa using tail_radius_pos different (0 : unitInterval) (by change (0 : ℝ) < 1; norm_num)
  let p := chart.origin + P.surfaceDist a b • direction α
  let q := chart.origin + P.surfaceDist a b • direction β
  let y := chart.origin + L • direction ((α + β) / 2)
  have at_y := circular_gap_voronoi_ray chart.sources chart.origin source_positive length_positive
    ordered one_turn first second empty_gap
  have y_radius : dist chart.origin y = L := by
    rw [dist_comm, dist_eq_norm, add_sub_cancel_left, norm_smul, direction_norm, mul_one,
      Real.norm_eq_abs, abs_of_pos length_positive]
  have base : chart.origin ≠ y := by
    intro same
    rw [same, dist_self] at y_radius
    linarith
  have base_length : dist M.left M.right = dist chart.origin y := by
    rw [M.base_length, u_eq, y_radius]
  have left_length : dist M.first M.left = dist p chart.origin := by
    have actual : dist M.first M.left = P.surfaceDist a (T.closedEdgeTarget edge 0) := by
      simpa using M.first_distances 0
    rw [T.closedEdgeTarget_zero, at_junction] at actual
    rw [chart.source_distance p first]
    exact actual
  obtain ⟨t, tp, _, _, _, inside, mapped⟩ := chart.incident_edge_sample T edge at_junction
    positive (show (0 : ℝ) < 1 by norm_num) on_ray
  let x := chart.origin + ((t : ℝ) * L) • direction ((α + β) / 2)
  have x_line : x = AffineMap.lineMap chart.origin y (t : ℝ) := by
    simp only [x, y, AffineMap.lineMap_apply_module]
    module
  have actual_distance : P.surfaceDist a (chart.map x) = dist p x := by
    exact (chart.gap_distance_iff different ordered one_turn (mul_pos tp length_positive)
      first second empty_gap inside first).mpr (Or.inl rfl)
  have sample : dist M.first (AffineMap.lineMap M.left M.right (t : ℝ)) =
      dist p (AffineMap.lineMap chart.origin y (t : ℝ)) := by
    rw [M.first_distances, ← mapped, actual_distance, ← x_line]
  have right_length := right_distance_eq_of_sample M.first M.left M.right p chart.origin y
    (show (t : ℝ) ≠ 0 from (show (0 : ℝ) < t from tp).ne') base_length left_length sample
  exact exists_bisector_motion M.left M.right M.first M.second chart.origin y p q base
    M.distinct_sources at_y.1 base_length left_length right_length M.left_distances M.right_distances
    ((chart.source_distance p first).trans (chart.source_distance q second).symm) at_y.2.2.1.1

/-- The same placement can respect either ordering of the two actual
branch labels. No orientation choice is hidden in an unordered source pair. -/
theorem incident_metric_placement_with_labels (T : P.CutLocusTree a)
    {u v : T.vertices} (edge : T.graph.Adj u v) (at_junction : T.vertexTarget u = b)
    (M : CutEdgeMetricModel T edge)
    {α β ε : ℝ} (ordered : α < β) (one_turn : β < α + 2 * π)
    (first : chart.origin + P.surfaceDist a b • direction α ∈ chart.sources)
    (second : chart.origin + P.surfaceDist a b • direction β ∈ chart.sources)
    (empty_gap : ∀ s ∈ chart.sources, ∃ φ ∈ Icc β (α + 2 * π),
      s = chart.origin + P.surfaceDist a b • direction φ)
    (positive : 0 < ε)
    (on_ray : ∀ ρ ∈ Ioo (0 : ℝ) ε,
      chart.map (chart.origin + ρ • direction ((α + β) / 2)) ∈
        openSegment ℝ (b : Space) (v : Space))
    (p q : Plane) (distinct : p ≠ q)
    (labels : ({p, q} : Set Plane) =
      {chart.origin + P.surfaceDist a b • direction α,
        chart.origin + P.surfaceDist a b • direction β}) :
    ∃ motion : Plane ≃ᵃⁱ[ℝ] Plane,
      motion M.left = chart.origin ∧
      motion M.right = chart.origin + dist (b : Space) (v : Space) • direction ((α + β) / 2) ∧
      motion M.first = p ∧ motion M.second = q := by
  have p_end : p = chart.origin + P.surfaceDist a b • direction α ∨
      p = chart.origin + P.surfaceDist a b • direction β := by
    have member : p ∈ ({p, q} : Set Plane) := by simp
    rwa [labels] at member
  have q_end : q = chart.origin + P.surfaceDist a b • direction α ∨
      q = chart.origin + P.surfaceDist a b • direction β := by
    have member : q ∈ ({p, q} : Set Plane) := by simp
    rwa [labels] at member
  rcases p_end with p_first | p_second <;> rcases q_end with q_first | q_second
  · exact (distinct (p_first.trans q_first.symm)).elim
  · rw [p_first, q_second]
    exact chart.incident_metric_placement T edge at_junction M ordered one_turn first second
      empty_gap positive on_ray
  · let swapped : CutEdgeMetricModel T edge := {
      M with
      first := M.second
      second := M.first
      distinct_sources := M.distinct_sources.symm
      first_distances := M.second_distances
      second_distances := M.first_distances }
    obtain ⟨motion, left, right, at_second, at_first⟩ :=
      chart.incident_metric_placement T edge at_junction swapped ordered one_turn first second
        empty_gap positive on_ray
    exact ⟨motion, left, right, at_first.trans p_second.symm, at_second.trans q_first.symm⟩
  · exact (distinct (p_second.trans q_second.symm)).elim

end SixVertexUnfolding.ConvexPolyhedron.CutVoronoiChart
