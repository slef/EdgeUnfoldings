import SixVertexUnfolding.Geometry.JunctionBranchSources
import SixVertexUnfolding.Geometry.SmallPolyhedronRouteBranchSeparation
import SixVertexUnfolding.Geometry.SmallPolyhedronShortestRoutes

/-! The limiting source of a continuous branch on an incident cut edge
is one of the two sources bounding that edge's angular gap.

Here the shortest-route inputs come from the actual vertex fans of a
polyhedron with at most six vertices and triangular/quadrilateral faces.
No canonical graph model is assumed. -/

namespace SixVertexUnfolding.ConvexPolyhedron.CutVoronoiChart

open Real Set

variable {P : ConvexPolyhedron} {a b : frontier P.body} (chart : P.CutVoronoiChart a b)

theorem small_incident_branch_sources (size : P.vertices.card ≤ 6)
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
  have finite := small_geodesicFiber_finite size small_faces a b different
  obtain ⟨p, hp, represents_left⟩ := chart.route_has_source finite ⟨left 0, endpoints.1⟩
  obtain ⟨q, hq, represents_right⟩ := chart.route_has_source finite ⟨right 0, endpoints.2⟩
  have routes_different : left 0 ≠ right 0 := by
    apply small_route_branches_distinct_at_zero size small_faces a (T.closedEdgeTarget edge) left right
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

end SixVertexUnfolding.ConvexPolyhedron.CutVoronoiChart
