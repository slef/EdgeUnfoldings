import SixVertexUnfolding.Geometry.JunctionMetricTriangles
import SixVertexUnfolding.Geometry.RadialTriangleMotions

/-! Incident metric placements retain the actual endpoint-route labels.
Any two placements using the same chart therefore agree along a shared
endpoint route, including portions outside that local chart.
-/

namespace SixVertexUnfolding.ConvexPolyhedron.CutVoronoiChart

open Real Set

variable {P : ConvexPolyhedron} {a b : frontier P.body} (chart : P.CutVoronoiChart a b)

/-- Choose the metric placement with its two actual limiting route labels. -/
theorem incident_placement_with_routes (graph : P.SixVertexGraph)
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
    chart.incident_branch_sources graph small_faces T edge at_junction not_vertex S left right
      agrees member ordered one_turn first second empty_gap positive on_ray
  obtain ⟨motion, at_left, at_right, at_first, at_second⟩ :=
    chart.incident_metric_placement_with_labels T edge at_junction M ordered one_turn first second
      empty_gap positive on_ray p q distinct pair
  exact ⟨motion, at_left, at_right, at_first.symm ▸ left_label, at_second.symm ▸ right_label⟩

/-- Common chart labels force agreement on the entire shared route,
not only on the small terminal portion represented inside the chart. -/
theorem incident_placements_agree
    {routes other : C(unitInterval, P.BoundaryCurve)} {p l r q u v : Plane}
    (D : RadialStripTriangle routes p l r) (E : RadialStripTriangle other q u v)
    (first second : Plane ≃ᵃⁱ[ℝ] Plane)
    (first_target : first l = chart.origin) (second_target : second u = chart.origin)
    (first_label : chart.Represents (first p) (routes 0))
    (second_label : chart.Represents (second q) (other 0))
    (same_route : routes 0 = other 0) :
    ∀ x ∈ range (routes 0), ∀ hx : x ∈ range (closedRouteStripMap routes),
      ∀ hy : x ∈ range (closedRouteStripMap other),
        first (D.homeomorph ⟨x, hx⟩) = second (E.homeomorph ⟨x, hy⟩) := by
  have source_same : first p = second q := chart.represented_source_unique
    first_label (same_route.symm ▸ second_label)
  have agreement := (D.move first).agrees_on_shared_route (E.move second)
    (AffineIsometryEquiv.refl ℝ Plane) 0 0 same_route source_same (by
      simpa using first_target.trans second_target.symm)
  simpa only [RadialStripTriangle.move_apply] using agreement

/-- Selecting the common source label also supplies equality of the actual
routes; it need not be assumed independently by an assembly argument. -/
theorem incident_placements_agree_of_source
    (finite_routes : (P.geodesicFiber a b).Finite)
    {routes other : C(unitInterval, P.BoundaryCurve)} {p l r q u v : Plane}
    (D : RadialStripTriangle routes p l r) (E : RadialStripTriangle other q u v)
    (first second : Plane ≃ᵃⁱ[ℝ] Plane)
    (first_target : first l = chart.origin) (second_target : second u = chart.origin)
    (first_member : routes 0 ∈ P.geodesicFiber a b)
    (second_member : other 0 ∈ P.geodesicFiber a b)
    (first_label : chart.Represents (first p) (routes 0))
    (second_label : chart.Represents (second q) (other 0))
    (same_source : first p = second q) :
    routes 0 = other 0 ∧
      ∀ x ∈ range (routes 0), ∀ hx : x ∈ range (closedRouteStripMap routes),
        ∀ hy : x ∈ range (closedRouteStripMap other),
          first (D.homeomorph ⟨x, hx⟩) = second (E.homeomorph ⟨x, hy⟩) := by
  have same_route := chart.represented_routes_agree finite_routes first_member second_member
    first_label (same_source.symm ▸ second_label)
  exact ⟨same_route, chart.incident_placements_agree D E first second first_target second_target
    first_label second_label same_route⟩

end SixVertexUnfolding.ConvexPolyhedron.CutVoronoiChart
