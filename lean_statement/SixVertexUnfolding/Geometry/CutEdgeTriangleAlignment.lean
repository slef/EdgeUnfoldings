import SixVertexUnfolding.Geometry.RadialTriangleMotions
import SixVertexUnfolding.Geometry.CutEdgeTriangleDevelopments
import SixVertexUnfolding.Geometry.SuccessiveRadialTriangles

/-! The equal length needed to join radial triangles is supplied by
their actual intrinsic-distance profiles. Either side of each kite is allowed. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

namespace CutEdgeMetricModel

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a}
  {u v : T.vertices} {edge : T.graph.Adj u v} (M : CutEdgeMetricModel T edge)

/-- Either source copy has the actual source-to-target distance. -/
theorem source_distance (p : Plane) (source : p ∈ ({M.first, M.second} : Set Plane))
    (t : unitInterval) :
    dist p (AffineMap.lineMap M.left M.right (t : ℝ)) = P.surfaceDist a (T.closedEdgeTarget edge t) := by
  rcases source with rfl | rfl
  · exact M.first_distances t
  · exact M.second_distances t

theorem source_noncollinear (p : Plane) (source : p ∈ ({M.first, M.second} : Set Plane)) :
    ¬ Collinear ℝ ({p, M.left, M.right} : Set Plane) := by
  rcases source with rfl | rfl
  · exact M.noncollinear.1
  · exact M.noncollinear.2

/-- Triangle developments sharing a route can be joined without any additional metric premise. -/
theorem align_shared_route {w z : T.vertices} {next : T.graph.Adj w z}
    (N : CutEdgeMetricModel T next)
    {routes other : C(unitInterval, P.BoundaryCurve)} {p q : Plane}
    (first_source : p ∈ ({M.first, M.second} : Set Plane))
    (second_source : q ∈ ({N.first, N.second} : Set Plane))
    (D : RadialStripTriangle routes p M.left M.right)
    (E : RadialStripTriangle other q N.left N.right)
    (s t : unitInterval) (same_target : T.closedEdgeTarget edge s = T.closedEdgeTarget next t)
    (same_route : routes s = other t) :
    ∃ motion : Plane ≃ᵃⁱ[ℝ] Plane, motion p = q ∧
      ∀ x ∈ range (routes s), ∀ hx : x ∈ range (closedRouteStripMap routes),
        ∀ hy : x ∈ range (closedRouteStripMap other),
          ((D.move motion).homeomorph ⟨x, hx⟩ : Plane) = (E.homeomorph ⟨x, hy⟩ : Plane) := by
  apply D.move_agrees_on_shared_route E s t same_route
  rw [M.source_distance p first_source, N.source_distance q second_source, same_target]

/-- Along successive tree edges, the actual source-distance profiles give an exact outward join. -/
theorem align_successive {w : T.vertices} {next : T.graph.Adj v w}
    (N : CutEdgeMetricModel T next)
    {routes other : C(unitInterval, P.BoundaryCurve)} {p q : Plane}
    (first_source : p ∈ ({M.first, M.second} : Set Plane))
    (second_source : q ∈ ({N.first, N.second} : Set Plane))
    (D : RadialStripTriangle routes p M.left M.right)
    (E : RadialStripTriangle other q N.left N.right)
    (same_route : routes 1 = other 0) :
    ∃ motion : Plane ≃ᵃⁱ[ℝ] Plane, motion p = q ∧ motion M.right = N.left ∧
      (∀ x ∈ range (routes 1), ∀ hx : x ∈ range (closedRouteStripMap routes),
        ∀ hy : x ∈ range (closedRouteStripMap other),
          ((D.move motion).homeomorph ⟨x, hx⟩ : Plane) = (E.homeomorph ⟨x, hy⟩ : Plane)) ∧
      convexHull ℝ ({motion p, motion M.left, motion M.right} : Set Plane) ∩
        convexHull ℝ ({q, N.left, N.right} : Set Plane) = segment ℝ q N.left := by
  apply D.align_successive_exact E same_route ?_
    (M.source_noncollinear p first_source) (N.source_noncollinear q second_source)
  have first := M.source_distance p first_source 1
  have second := N.source_distance q second_source 0
  simp [T.closedEdgeTarget_one, T.closedEdgeTarget_zero] at first second
  exact first.trans second.symm

end CutEdgeMetricModel
end SixVertexUnfolding.ConvexPolyhedron
