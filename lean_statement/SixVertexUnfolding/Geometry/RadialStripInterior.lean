import SixVertexUnfolding.Geometry.RadialStripDevelopments
import SixVertexUnfolding.Geometry.TriangleFanInterior

/-! The open surface strip maps exactly to the ordinary planar triangle
interior; the endpoint rays, source, and terminal edge map to its boundary. -/

namespace SixVertexUnfolding.ConvexPolyhedron.RadialStripTriangle

open Set

variable {P : ConvexPolyhedron} {routes : C(unitInterval, P.BoundaryCurve)} {p l r : Plane}
  (D : RadialStripTriangle routes p l r)

/-- The planar interior corresponds precisely to the original open route strip. -/
theorem interior_iff_open_strip (noncollinear : ¬ Collinear ℝ ({p, l, r} : Set Plane))
    (open_routes : C(Ioo (0 : ℝ) 1, P.BoundaryCurve))
    (agrees : ∀ t, routes (interiorTime t) = open_routes t)
    (x : range (closedRouteStripMap routes)) :
    (D.homeomorph x : Plane) ∈ interior (convexHull ℝ ({p, l, r} : Set Plane)) ↔ x.val ∈ routeStrip open_routes := by
  constructor
  · intro interior
    obtain ⟨z, at_x⟩ := x.property
    have same : (⟨closedRouteStripMap routes z, mem_range_self z⟩ : range (closedRouteStripMap routes)) = x :=
      Subtype.ext at_x
    have coordinate := D.radial z
    rw [same] at coordinate
    rw [coordinate] at interior
    obtain ⟨base_positive, base_before, time_positive, time_before⟩ :=
      (triangleFan_interior_iff p l r noncollinear z).mp interior
    refine ⟨(⟨z.1, base_positive, base_before⟩, ⟨z.2, time_positive, time_before⟩), ?_⟩
    change open_routes ⟨z.1, base_positive, base_before⟩ z.2 = x.val
    rw [← agrees]
    exact at_x
  · rintro ⟨⟨t, s⟩, at_x⟩
    let z := (interiorTime t, interiorTime s)
    have same : (⟨closedRouteStripMap routes z, mem_range_self z⟩ : range (closedRouteStripMap routes)) = x := by
      apply Subtype.ext
      change routes (interiorTime t) (interiorTime s) = x.val
      rw [agrees]
      exact at_x
    have coordinate := D.radial z
    rw [same] at coordinate
    rw [coordinate]
    exact (triangleFan_interior_iff p l r noncollinear z).mpr
      ⟨t.property.1, t.property.2, s.property.1, s.property.2⟩

end SixVertexUnfolding.ConvexPolyhedron.RadialStripTriangle
