import SixVertexUnfolding.Geometry.PlacedRayTargets
import SixVertexUnfolding.Geometry.SmallPolyhedronClosedCutRayIntersections

/-! Away from the source, all triangle representations of a surface
point have the same terminal cut point.
This version uses at most six vertices and triangular/quadrilateral faces,
without a canonical graph assumption. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

variable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include size small_faces

/-- The terminal cut point is intrinsic, independently of its triangle coordinates. -/
theorem small_placed_ray_targets_equal {a : frontier P.body} {T : P.CutLocusTree a}
    {u v w z : T.vertices} {edge : T.graph.Adj u v} {other : T.graph.Adj w z}
    (D : PlacedCutEdgeTriangles T edge) (E : PlacedCutEdgeTriangles T other)
    {s t : unitInterval} {b : frontier P.body} {x y : Plane} (not_source : b ≠ a)
    (first : D.PlacesOnRay s b x) (second : E.PlacesOnRay t b y) :
    T.closedEdgeTarget edge s = T.closedEdgeTarget other t := by
  obtain ⟨side, time, at_point, _⟩ := first
  obtain ⟨other_side, other_time, other_point, _⟩ := second
  have first_member := D.routes_member side s
  have second_member := E.routes_member other_side t
  have meet := (small_closed_cut_rays_intersection size small_faces a
    (T.closedEdgeTarget edge s) (T.closedEdgeTarget other t)
    (T.closedEdgeTarget_cut edge s) (T.closedEdgeTarget_cut other t)
    (D.routes side s) (E.routes other_side t) first_member second_member b).mp
      ⟨⟨time, at_point⟩, ⟨other_time, other_point⟩⟩
  rcases meet with source | ⟨targets, _⟩ | ⟨same_route, _⟩
  · exact (not_source source).elim
  · exact targets
  · exact (congrArg Prod.snd first_member.2).symm.trans
      ((congrArg (fun route : P.BoundaryCurve => route 1) same_route).trans
        (congrArg Prod.snd second_member.2))

end SixVertexUnfolding.ConvexPolyhedron
