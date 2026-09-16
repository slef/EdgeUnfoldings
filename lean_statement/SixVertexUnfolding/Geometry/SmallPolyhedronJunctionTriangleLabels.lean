import SixVertexUnfolding.Geometry.JunctionTriangleLabels
import SixVertexUnfolding.Geometry.SmallPolyhedronJunctionBranchSources

/-! Incident metric placements retain the actual endpoint-route labels.
Any two placements using the same chart therefore agree along a shared
endpoint route, including portions outside that local chart.

Here the shortest-route inputs come from the actual vertex fans of a
polyhedron with at most six vertices and triangular/quadrilateral faces.
No canonical graph model is assumed. -/

namespace SixVertexUnfolding.ConvexPolyhedron.CutVoronoiChart

open Real Set

variable {P : ConvexPolyhedron} {a b : frontier P.body} (chart : P.CutVoronoiChart a b)

theorem small_incident_placement_with_routes (size : P.vertices.card ≤ 6)
    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4)
    (T : P.CutLocusTree a) {u v : T.vertices} (edge : T.graph.Adj u v)
    (at_junction : T.vertexTarget u = b) (not_vertex : (b : Space) ∉ P.vertices)
    (M : CutEdgeMetricModel T edge) (S : CutEdgeStrips T edge)
    (left right : C(unitInterval, P.BoundaryCurve))
    (agrees : ∀ t, left (interiorTime t) = S.first t ∧ right (interiorTime t) = S.second t)
    (member : ∀ t, left t ∈ P.geodesicFiber a (T.closedEdgeTarget edge t) ∧
      right t ∈ P.geodesicFiber a (T.closedEdgeTarget edge t))
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
      chart.Represents (motion M.first) (left 0) ∧
      chart.Represents (motion M.second) (right 0) := by
  obtain ⟨p, _, q, _, left_label, right_label, distinct, pair⟩ :=
    chart.small_incident_branch_sources size small_faces T edge at_junction not_vertex S left right
      agrees member ordered one_turn first second empty_gap positive on_ray
  obtain ⟨motion, at_left, at_right, at_first, at_second⟩ :=
    chart.incident_metric_placement_with_labels T edge at_junction M ordered one_turn first second
      empty_gap positive on_ray p q distinct pair
  exact ⟨motion, at_left, at_right, at_first.symm ▸ left_label, at_second.symm ▸ right_label⟩

end SixVertexUnfolding.ConvexPolyhedron.CutVoronoiChart
