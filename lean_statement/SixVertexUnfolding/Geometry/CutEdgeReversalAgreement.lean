import SixVertexUnfolding.Geometry.CutEdgeRouteReversal
import SixVertexUnfolding.Geometry.CutEdgeReversalMotion
import SixVertexUnfolding.Geometry.RadialTriangleReversal

/-! The complete pair of triangle developments agrees across an edge
after one rigid motion and one consistent choice of source labels. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

namespace RadialStripTriangle

/-- Two coordinate maps describe the same surface points after a prescribed motion. -/
def AgreesAfter {P : ConvexPolyhedron} {routes other : C(unitInterval, P.BoundaryCurve)}
    {p l r q L R : Plane} (D : RadialStripTriangle routes p l r)
    (E : RadialStripTriangle other q L R) (motion : Plane ≃ᵃⁱ[ℝ] Plane) : Prop :=
  range (closedRouteStripMap routes) = range (closedRouteStripMap other) ∧
    ∀ x : frontier P.body, ∀ hx : x ∈ range (closedRouteStripMap routes),
      ∀ hy : x ∈ range (closedRouteStripMap other),
        motion (D.homeomorph ⟨x, hx⟩) = (E.homeomorph ⟨x, hy⟩ : Plane)

/-- Reversal supplies agreement on the entire surface region. -/
theorem agreesAfter_of_reversal {P : ConvexPolyhedron} {routes other : C(unitInterval, P.BoundaryCurve)}
    {p l r q L R : Plane} (D : RadialStripTriangle routes p l r)
    (E : RadialStripTriangle other q L R) (same : ∀ t, routes t = other (unitInterval.symm t))
    (motion : Plane ≃ᵃⁱ[ℝ] Plane) (source : motion p = q)
    (left : motion l = R) (right : motion r = L) : D.AgreesAfter E motion :=
  ⟨reversed_family_range same, D.reversed_developments_agree E same motion source left right⟩

end RadialStripTriangle

namespace CutEdgeTriangles

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a}
    {u v : T.vertices} {edge : T.graph.Adj u v}
    (D : CutEdgeTriangles T edge) (E : CutEdgeTriangles T edge.symm)

/-- One motion aligns both actual triangles, not independent motions for each side. -/
theorem reversal_agreement :
    ∃ motion : Plane ≃ᵃⁱ[ℝ] Plane,
      motion D.model.left = E.model.right ∧ motion D.model.right = E.model.left ∧
      ((motion D.model.first = E.model.first ∧ motion D.model.second = E.model.second ∧
        (∀ t, D.first t = E.first (unitInterval.symm t)) ∧
        (∀ t, D.second t = E.second (unitInterval.symm t)) ∧
        D.first_triangle.AgreesAfter E.first_triangle motion ∧
        D.second_triangle.AgreesAfter E.second_triangle motion) ∨
       (motion D.model.first = E.model.second ∧ motion D.model.second = E.model.first ∧
        (∀ t, D.first t = E.second (unitInterval.symm t)) ∧
        (∀ t, D.second t = E.first (unitInterval.symm t)) ∧
        D.first_triangle.AgreesAfter E.second_triangle motion ∧
        D.second_triangle.AgreesAfter E.first_triangle motion)) := by
  rcases D.reversed_route_families E with same | swapped
  · obtain ⟨motion, left, right, first, second⟩ := D.model.exists_reversal_motion E.model
    exact ⟨motion, left, right, Or.inl ⟨first, second, same.1, same.2,
      D.first_triangle.agreesAfter_of_reversal E.first_triangle same.1 motion first left right,
      D.second_triangle.agreesAfter_of_reversal E.second_triangle same.2 motion second left right⟩⟩
  · obtain ⟨motion, left, right, first, second⟩ := D.model.exists_swapped_reversal_motion E.model
    exact ⟨motion, left, right, Or.inr ⟨first, second, swapped.1, swapped.2,
      D.first_triangle.agreesAfter_of_reversal E.second_triangle swapped.1 motion first left right,
      D.second_triangle.agreesAfter_of_reversal E.first_triangle swapped.2 motion second left right⟩⟩

end CutEdgeTriangles
end SixVertexUnfolding.ConvexPolyhedron
