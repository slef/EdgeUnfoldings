import SixVertexUnfolding.Geometry.JunctionTriangleLabels
import SixVertexUnfolding.Geometry.JunctionTriangleSectors
import SixVertexUnfolding.Geometry.IncidentStripIntersections
import SixVertexUnfolding.Geometry.IncidentRadialDevelopments

/-! Adjacent triangles placed in a common nonvertex junction chart
join with their prescribed motions. The shared route and both exact
intersections are derived from the actual branch labels and angular order.
-/

namespace SixVertexUnfolding.ConvexPolyhedron.CutVoronoiChart

open Real Set

variable {P : ConvexPolyhedron} {a b : frontier P.body} (chart : P.CutVoronoiChart a b)

/-- The common chart supplies a genuine two-triangle join, without
choosing a new reflection independently for this pair. -/
theorem join_incident_triangles (graph : P.SixVertexGraph)
    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4)
    (T : P.CutLocusTree a) {u v w : T.vertices}
    (edge : T.graph.Adj u v) (next : T.graph.Adj u w) (distinct : v ≠ w)
    (at_junction : T.vertexTarget u = b)
    {routes other : C(unitInterval, P.BoundaryCurve)} {p l r q L R : Plane}
    (D : RadialStripTriangle routes p l r) (E : RadialStripTriangle other q L R)
    (member : ∀ t, routes t ∈ P.geodesicFiber a (T.closedEdgeTarget edge t))
    (other_member : ∀ t, other t ∈ P.geodesicFiber a (T.closedEdgeTarget next t))
    (first second : Plane ≃ᵃⁱ[ℝ] Plane) {α β γ : ℝ}
    (first_gap : α < β) (second_gap : β < γ)
    (first_width : β < α + 2 * π) (second_width : γ < β + 2 * π)
    (first_target : first l = chart.origin) (second_target : second L = chart.origin)
    (first_base : first r = chart.origin + dist (b : Space) (v : Space) • direction ((α + β) / 2))
    (second_base : second R = chart.origin + dist (b : Space) (w : Space) • direction ((β + γ) / 2))
    (first_source : first p = chart.origin + P.surfaceDist a b • direction β)
    (second_source : second q = chart.origin + P.surfaceDist a b • direction β)
    (first_label : chart.Represents (first p) (routes 0))
    (second_label : chart.Represents (second q) (other 0)) :
    ∃ joined : (range (closedRouteStripMap routes) ∪ range (closedRouteStripMap other) :
        Set (frontier P.body)) ≃ₜ
      (convexHull ℝ ({first p, first l, first r} : Set Plane) ∪
        convexHull ℝ ({second q, second L, second R} : Set Plane) : Set Plane),
      (∀ x : range (closedRouteStripMap routes),
        (joined ⟨x, Or.inl x.property⟩ : Plane) = first (D.homeomorph x)) ∧
      (∀ y : range (closedRouteStripMap other),
        (joined ⟨y, Or.inr y.property⟩ : Plane) = second (E.homeomorph y)) := by
  have different : a ≠ b := at_junction ▸ T.vertexTarget_different u
  have source_same : first p = second q := first_source.trans second_source.symm
  have target_same : first l = second L := first_target.trans second_target.symm
  have first_member : routes 0 ∈ P.geodesicFiber a b := by
    simpa only [T.closedEdgeTarget_zero, at_junction] using member 0
  have second_member : other 0 ∈ P.geodesicFiber a b := by
    simpa only [T.closedEdgeTarget_zero, at_junction] using other_member 0
  have same_route := chart.represented_routes_agree
    (graph.geodesicFiber_finite small_faces a b different) first_member second_member
    first_label (source_same.symm ▸ second_label)
  have surface_intersection := graph.incident_strips_intersection_of_shared_route small_faces
    a T edge next distinct routes other member other_member same_route
  have radius_positive : 0 < P.surfaceDist a b := by
    simpa using tail_radius_pos different (0 : unitInterval) (by change (0 : ℝ) < 1; norm_num)
  have u_eq : (u : Space) = (b : Space) := congrArg Subtype.val at_junction
  have edge_positive {z : T.vertices} (adjacent : T.graph.Adj u z) :
      0 < dist (b : Space) (z : Space) := by
    apply dist_pos.mpr
    intro same
    exact adjacent.ne (Subtype.ext (u_eq.trans same))
  have planar_intersection :
      convexHull ℝ ({first p, first l, first r} : Set Plane) ∩
        convexHull ℝ ({second q, second L, second R} : Set Plane) = segment ℝ (second q) (second L) := by
    rw [first_source, second_source, first_target, second_target, first_base, second_base]
    exact consecutive_gap_triangles_intersection chart.origin radius_positive
      (edge_positive edge) (edge_positive next) first_gap second_gap first_width second_width
  exact (D.move first).glue_incident (E.move second) same_route source_same target_same
    surface_intersection planar_intersection

end SixVertexUnfolding.ConvexPolyhedron.CutVoronoiChart
