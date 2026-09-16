import SixVertexUnfolding.Geometry.GlueCompactDevelopments
import SixVertexUnfolding.Geometry.RadialTriangleMotions

/-! Exact surface and planar boundary intersections allow two radial
developments to be pasted into one homeomorphism of their unions. -/

namespace SixVertexUnfolding.ConvexPolyhedron.RadialStripTriangle

open Set

variable {P : ConvexPolyhedron}
  {routes other : C(unitInterval, P.BoundaryCurve)} {p l r q u v : Plane}
  (D : RadialStripTriangle routes p l r) (E : RadialStripTriangle other q u v)

/-- Join two aligned radial developments, retaining their exact original coordinate maps. -/
theorem glue_successive (same_route : routes 1 = other 0) (at_source : p = q) (at_target : r = u)
    (surface_intersection : range (closedRouteStripMap routes) ∩ range (closedRouteStripMap other) =
      range (routes 1))
    (planar_intersection : convexHull ℝ ({p, l, r} : Set Plane) ∩
      convexHull ℝ ({q, u, v} : Set Plane) = segment ℝ q u) :
    ∃ joined : (range (closedRouteStripMap routes) ∪ range (closedRouteStripMap other) : Set (frontier P.body)) ≃ₜ
        (convexHull ℝ ({p, l, r} : Set Plane) ∪ convexHull ℝ ({q, u, v} : Set Plane) : Set Plane),
      (∀ x : range (closedRouteStripMap routes),
        (joined ⟨x, Or.inl x.property⟩ : Plane) = (D.homeomorph x : Plane)) ∧
      (∀ y : range (closedRouteStripMap other),
        (joined ⟨y, Or.inr y.property⟩ : Plane) = (E.homeomorph y : Plane)) := by
  subst q
  subst u
  apply glue_compact_developments _ _ _ _
    (isCompact_range (closedRouteStripMap routes).continuous)
    (isCompact_range (closedRouteStripMap other).continuous) D.homeomorph E.homeomorph
  intro x y
  have left_ray (time : unitInterval) :
      (D.homeomorph ⟨closedRouteStripMap routes (1, time), mem_range_self _⟩ : Plane) =
        AffineMap.lineMap p r (time : ℝ) := by
    simpa [triangleFanMap] using D.radial (1, time)
  have right_ray (time : unitInterval) :
      (E.homeomorph ⟨closedRouteStripMap other (0, time), mem_range_self _⟩ : Plane) =
        AffineMap.lineMap p r (time : ℝ) := by
    simpa [triangleFanMap] using E.radial (0, time)
  constructor
  · intro same
    have hy : x.val ∈ range (closedRouteStripMap other) := same.symm ▸ y.property
    have inside : x.val ∈ range (routes 1) := surface_intersection ▸ ⟨x.property, hy⟩
    have agrees := D.agrees_on_shared_route E (AffineIsometryEquiv.refl ℝ Plane) 1 0
      same_route rfl (by simp) x.val inside x.property hy
    have right_point : (⟨x.val, hy⟩ : range (closedRouteStripMap other)) = y := Subtype.ext same
    simpa only [right_point] using agrees
  · intro same
    have common : (D.homeomorph x : Plane) ∈ segment ℝ p r := by
      rw [← planar_intersection]
      exact ⟨(D.homeomorph x).property, same.symm ▸ (E.homeomorph y).property⟩
    rw [segment_eq_image_lineMap] at common
    obtain ⟨time, in_interval, at_time⟩ := common
    let t : unitInterval := ⟨time, in_interval⟩
    have left_point : x = ⟨closedRouteStripMap routes (1, t), mem_range_self _⟩ := by
      apply D.homeomorph.injective
      exact Subtype.ext ((left_ray t).trans at_time).symm
    have right_point : y = ⟨closedRouteStripMap other (0, t), mem_range_self _⟩ := by
      apply E.homeomorph.injective
      exact Subtype.ext (((right_ray t).trans at_time).trans same).symm
    rw [left_point, right_point]
    change routes 1 t = other 0 t
    rw [same_route]

end SixVertexUnfolding.ConvexPolyhedron.RadialStripTriangle
