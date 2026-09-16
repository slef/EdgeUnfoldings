import SixVertexUnfolding.Geometry.JoinedRadialDevelopments
import SixVertexUnfolding.Geometry.CutEdgeTriangleAlignment
import SixVertexUnfolding.Geometry.SuccessiveStripIntersections

/-! Two successive actual cut-tree strips sharing an endpoint route
admit a single planar development, with exactly the prescribed triangle maps. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- A joined pair retains both radial developments and their exact common boundary. -/
structure RadialTriangleJoin {P : ConvexPolyhedron}
    {routes other : C(unitInterval, P.BoundaryCurve)} {p l r q u v : Plane}
    (D : RadialStripTriangle routes p l r) (E : RadialStripTriangle other q u v) where
  motion : Plane ≃ᵃⁱ[ℝ] Plane
  source : motion p = q
  target : motion r = u
  homeomorph : (range (closedRouteStripMap routes) ∪ range (closedRouteStripMap other) :
    Set (frontier P.body)) ≃ₜ
      (convexHull ℝ ({motion p, motion l, motion r} : Set Plane) ∪
        convexHull ℝ ({q, u, v} : Set Plane) : Set Plane)
  first : ∀ x : range (closedRouteStripMap routes),
    (homeomorph ⟨x, Or.inl x.property⟩ : Plane) = motion (D.homeomorph x)
  second : ∀ y : range (closedRouteStripMap other),
    (homeomorph ⟨y, Or.inr y.property⟩ : Plane) = (E.homeomorph y : Plane)
  intersection : convexHull ℝ ({motion p, motion l, motion r} : Set Plane) ∩
    convexHull ℝ ({q, u, v} : Set Plane) = segment ℝ q u

namespace SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- The actual metric profiles and actual strip intersections supply the complete two-triangle join. -/
theorem join_successive_cut_tree_triangles (a : frontier P.body) (T : P.CutLocusTree a)
    {u v w : T.vertices} (first : T.graph.Adj u v) (second : T.graph.Adj v w) (no_return : u ≠ w)
    (M : CutEdgeMetricModel T first) (N : CutEdgeMetricModel T second)
    {routes other : C(unitInterval, P.BoundaryCurve)} {p q : Plane}
    (first_source : p ∈ ({M.first, M.second} : Set Plane))
    (second_source : q ∈ ({N.first, N.second} : Set Plane))
    (D : RadialStripTriangle routes p M.left M.right)
    (E : RadialStripTriangle other q N.left N.right)
    (member : ∀ t, routes t ∈ P.geodesicFiber a (T.closedEdgeTarget first t))
    (other_member : ∀ t, other t ∈ P.geodesicFiber a (T.closedEdgeTarget second t))
    (same_route : routes 1 = other 0) : Nonempty (RadialTriangleJoin D E) := by
  obtain ⟨motion, at_source, at_target, _, intersection⟩ :=
    M.align_successive N first_source second_source D E same_route
  have surface_intersection := graph.successive_strips_intersection_of_shared_route small_faces
    a T first second no_return routes other member other_member same_route
  obtain ⟨joined, on_first, on_second⟩ := (D.move motion).glue_successive E
    same_route at_source at_target surface_intersection intersection
  exact ⟨⟨motion, at_source, at_target, joined, on_first, on_second, intersection⟩⟩

end SixVertexGraph
end SixVertexUnfolding.ConvexPolyhedron
