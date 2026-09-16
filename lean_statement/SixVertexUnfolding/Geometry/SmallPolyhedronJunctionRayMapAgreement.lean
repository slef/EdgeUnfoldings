import SixVertexUnfolding.Geometry.JunctionRayMapAgreement
import SixVertexUnfolding.Geometry.SmallPolyhedronGlobalTriangleMaps

/-! In a fixed junction chart, every retained point of a shared
endpoint ray has one coordinate, even when different triangles name it.
This version uses at most six vertices and triangular/quadrilateral faces,
without a canonical graph assumption. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

variable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include size small_faces

/-- Two actual incident charts agree wherever their endpoint rays meet away from the source. -/
theorem small_incident_ray_placements_agree {a : frontier P.body} {T : P.CutLocusTree a}
    {u v w : T.vertices} {edge : T.graph.Adj u v} {other : T.graph.Adj u w}
    {chart : P.CutVoronoiChart a (T.vertexTarget u)} {angle other_angle : ℝ}
    (D : IncidentTriangles T edge chart angle) (E : IncidentTriangles T other chart other_angle)
    {b : frontier P.body} {x y : Plane} (not_source : b ≠ a)
    (first : D.placed.PlacesOnRay 0 b x) (second : E.placed.PlacesOnRay 0 b y) : x = y := by
  obtain ⟨side, time, first_point, first_position⟩ := first
  obtain ⟨other_side, other_time, second_point, second_position⟩ := second
  change AffineMap.lineMap (D.motion (D.apex side))
    (AffineMap.lineMap (D.motion D.model.left) (D.motion D.model.right) 0) (time : ℝ) = x at first_position
  change AffineMap.lineMap (E.motion (E.apex other_side))
    (AffineMap.lineMap (E.motion E.model.left) (E.motion E.model.right) 0) (other_time : ℝ) = y at second_position
  simp only [AffineMap.lineMap_apply_zero, D.at_junction] at first_position
  simp only [AffineMap.lineMap_apply_zero, E.at_junction] at second_position
  have first_member : D.routes side 0 ∈ P.geodesicFiber a (T.vertexTarget u) := by
    simpa only [T.closedEdgeTarget_zero] using D.routes_member side 0
  have second_member : E.routes other_side 0 ∈ P.geodesicFiber a (T.vertexTarget u) := by
    simpa only [T.closedEdgeTarget_zero] using E.routes_member other_side 0
  have first_injective := P.geodesicFiber_injective a (T.vertexTarget u)
    (T.vertexTarget_different u) (D.routes side 0) first_member
  have second_injective := P.geodesicFiber_injective a (T.vertexTarget u)
    (T.vertexTarget_different u) (E.routes other_side 0) second_member
  have meet := (small_closed_cut_rays_intersection size small_faces a (T.vertexTarget u) (T.vertexTarget u)
    (T.vertexTarget_cut u) (T.vertexTarget_cut u) (D.routes side 0) (E.routes other_side 0)
    first_member second_member b).mp ⟨⟨time, first_point⟩, ⟨other_time, second_point⟩⟩
  rcases meet with source | ⟨_, at_vertex⟩ | ⟨same_route, _⟩
  · exact (not_source source).elim
  · have first_last : time = 1 := first_injective
      ((first_point.trans at_vertex).trans (congrArg Prod.snd first_member.2).symm)
    have second_last : other_time = 1 := second_injective
      ((second_point.trans at_vertex).trans (congrArg Prod.snd second_member.2).symm)
    rw [first_last] at first_position
    rw [second_last] at second_position
    change AffineMap.lineMap (D.motion (D.apex side)) chart.origin (1 : ℝ) = x at first_position
    change AffineMap.lineMap (E.motion (E.apex other_side)) chart.origin (1 : ℝ) = y at second_position
    rw [AffineMap.lineMap_apply_one] at first_position second_position
    exact first_position.symm.trans second_position
  · have same_source := chart.represented_source_unique (D.route_label side)
      (same_route.symm ▸ E.route_label other_side)
    have same_time : time = other_time := first_injective
      ((first_point.trans second_point.symm).trans
        (congrArg (fun route : P.BoundaryCurve => route other_time) same_route).symm)
    rw [same_source, same_time] at first_position
    exact first_position.symm.trans second_position

/-- The fixed global frame preserves this full endpoint-ray agreement. -/
theorem small_global_incident_ray_placements_agree {a : frontier P.body} {T : P.CutLocusTree a}
    (charts : CutTreeCharts T) {u v w : T.vertices} (edge : T.graph.Adj u v) (other : T.graph.Adj u w)
    (nonvertex : (u : Space) ∉ P.vertices) {b : frontier P.body} {x y : Plane} (not_source : b ≠ a)
    (first : (charts.global edge).PlacesOnRay 0 b x)
    (second : (charts.global other).PlacesOnRay 0 b y) : x = y := by
  have first_local := ((charts.triangles edge).placesOnRay_inFrame (charts.frames.frame u) 0 b x).mp first
  have second_local := ((charts.triangles other).placesOnRay_inFrame (charts.frames.frame u) 0 b y).mp second
  rw [charts.at_fan edge nonvertex] at first_local
  rw [charts.at_fan other nonvertex] at second_local
  exact (charts.frames.frame u).symm.injective
    (small_incident_ray_placements_agree size small_faces _ _ not_source first_local second_local)

end SixVertexUnfolding.ConvexPolyhedron
