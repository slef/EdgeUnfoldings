import SixVertexUnfolding.Geometry.RadialStripDevelopments
import SixVertexUnfolding.Geometry.HingePlacement

/-! Two radial triangles can be aligned along a shared surface route.
The conclusion is agreement at every actual point of that route. -/

namespace SixVertexUnfolding.ConvexPolyhedron.RadialStripTriangle

open Set

variable {P : ConvexPolyhedron}
  {routes other : C(unitInterval, P.BoundaryCurve)} {p l r q u v : Plane}
  (D : RadialStripTriangle routes p l r) (E : RadialStripTriangle other q u v)

/-- A specified motion fixing both ray endpoints agrees along the shared surface route. -/
theorem agrees_on_shared_route (motion : Plane ≃ᵃⁱ[ℝ] Plane) (s t : unitInterval)
    (same_route : routes s = other t) (at_source : motion p = q)
    (at_target : motion (AffineMap.lineMap l r (s : ℝ)) = AffineMap.lineMap u v (t : ℝ)) :
    ∀ x ∈ range (routes s), ∀ hx : x ∈ range (closedRouteStripMap routes),
      ∀ hy : x ∈ range (closedRouteStripMap other),
        motion (D.homeomorph ⟨x, hx⟩) = (E.homeomorph ⟨x, hy⟩ : Plane) := by
  rintro x ⟨time, rfl⟩ hx hy
  have other_point :
      (⟨closedRouteStripMap other (t, time), mem_range_self _⟩ :
        range (closedRouteStripMap other)) = ⟨routes s time, hy⟩ := by
    apply Subtype.ext
    change other t time = routes s time
    rw [same_route]
  have radial_agreement :
      motion (D.homeomorph ⟨closedRouteStripMap routes (s, time), mem_range_self _⟩) =
        (E.homeomorph ⟨closedRouteStripMap other (t, time), mem_range_self _⟩ : Plane) := by
    rw [D.radial, E.radial]
    change motion.toAffineEquiv (AffineMap.lineMap p _ (time : ℝ)) = _
    rw [AffineEquiv.apply_lineMap]
    change AffineMap.lineMap (motion p) (motion (AffineMap.lineMap l r (s : ℝ))) (time : ℝ) = _
    rw [at_source, at_target]
    rfl
  simpa only [other_point] using radial_agreement

/-- Equal radial lengths let one rigid motion identify every matching radial parameter. -/
theorem align_radial_parameters (s t : unitInterval)
    (same_length : dist p (AffineMap.lineMap l r (s : ℝ)) =
      dist q (AffineMap.lineMap u v (t : ℝ))) :
    ∃ motion : Plane ≃ᵃⁱ[ℝ] Plane, motion p = q ∧ ∀ time : unitInterval,
      motion (D.homeomorph ⟨closedRouteStripMap routes (s, time), mem_range_self _⟩) =
        (E.homeomorph ⟨closedRouteStripMap other (t, time), mem_range_self _⟩ : Plane) := by
  obtain ⟨motion, at_source, at_target⟩ := exists_plane_motion p
    (AffineMap.lineMap l r (s : ℝ)) q (AffineMap.lineMap u v (t : ℝ)) same_length
  refine ⟨motion, at_source, fun time => ?_⟩
  rw [D.radial, E.radial]
  change motion.toAffineEquiv (AffineMap.lineMap p _ (time : ℝ)) =
    AffineMap.lineMap q _ (time : ℝ)
  rw [AffineEquiv.apply_lineMap]
  change AffineMap.lineMap (motion p) (motion (AffineMap.lineMap l r (s : ℝ))) (time : ℝ) = _
  rw [at_source, at_target]

/-- If the boundary routes are the same, the aligned developments agree along that whole route. -/
theorem align_shared_route (s t : unitInterval) (same_route : routes s = other t)
    (same_length : dist p (AffineMap.lineMap l r (s : ℝ)) =
      dist q (AffineMap.lineMap u v (t : ℝ))) :
    ∃ motion : Plane ≃ᵃⁱ[ℝ] Plane, motion p = q ∧
      ∀ x ∈ range (routes s), ∀ hx : x ∈ range (closedRouteStripMap routes),
        ∀ hy : x ∈ range (closedRouteStripMap other),
          motion (D.homeomorph ⟨x, hx⟩) = (E.homeomorph ⟨x, hy⟩ : Plane) := by
  obtain ⟨motion, at_source, aligned⟩ := D.align_radial_parameters E s t same_length
  refine ⟨motion, at_source, ?_⟩
  rintro x ⟨time, rfl⟩ hx hy
  have same_point : closedRouteStripMap other (t, time) = routes s time := by
    change other t time = routes s time
    rw [same_route]
  have other_point :
      (⟨closedRouteStripMap other (t, time), mem_range_self _⟩ :
        range (closedRouteStripMap other)) = ⟨routes s time, hy⟩ := Subtype.ext same_point
  simpa only [other_point] using aligned time

end SixVertexUnfolding.ConvexPolyhedron.RadialStripTriangle
