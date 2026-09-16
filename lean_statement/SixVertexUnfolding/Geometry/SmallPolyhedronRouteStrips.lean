import SixVertexUnfolding.Geometry.RouteStrips
import SixVertexUnfolding.Geometry.SmallPolyhedronCutRayCoordinates
import SixVertexUnfolding.Geometry.SmallPolyhedronTerminalRays

/-! The interiors swept out by continuously varying shortest routes.
These are actual surface regions, parametrized by a target and a time
strictly between the source and the cut endpoint.

Here the shortest-route inputs come from the actual vertex fans of a
polyhedron with at most six vertices and triangular/quadrilateral faces.
No canonical graph model is assumed. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set BoundedContinuousFunction

variable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include size small_faces in
/-- A strip parametrized by distinct cut endpoints has no self-identifications. -/
theorem small_routeStripMap_injective (a : frontier P.body) {X : Type*} [TopologicalSpace X]
    (target : X → frontier P.body) (injective_target : Function.Injective target)
    (cut : ∀ x, target x ∈ P.cutSet a) (routes : C(X, P.BoundaryCurve))
    (member : ∀ x, routes x ∈ P.geodesicFiber a (target x)) :
    Function.Injective (routeStripMap routes) := by
  rintro ⟨x, s⟩ ⟨y, t⟩ meet
  have same := small_cut_rays_meeting size small_faces a (target x) (target y) (cut x) (cut y)
    (routes x) (routes y) (member x) (member y) (interiorTime s) (interiorTime t)
    s.property.1 s.property.2 meet
  have times : s.val = t.val := congrArg (fun r : unitInterval => (r : ℝ)) same.2.1
  exact Prod.ext (injective_target same.1) (Subtype.ext times)

include size small_faces in
/-- Two distinct route branches over the same cut-edge targets sweep disjoint interiors. -/
theorem small_routeStrips_disjoint (a : frontier P.body) {X : Type*} [TopologicalSpace X]
    (target : X → frontier P.body) (injective_target : Function.Injective target)
    (cut : ∀ x, target x ∈ P.cutSet a) (first second : C(X, P.BoundaryCurve))
    (first_member : ∀ x, first x ∈ P.geodesicFiber a (target x))
    (second_member : ∀ x, second x ∈ P.geodesicFiber a (target x))
    (distinct : ∀ x, first x ≠ second x) : Disjoint (routeStrip first) (routeStrip second) := by
  apply disjoint_left.mpr
  rintro b ⟨⟨x, s⟩, hx⟩ ⟨⟨y, t⟩, hy⟩
  have same := small_cut_rays_meeting size small_faces a (target x) (target y) (cut x) (cut y)
    (first x) (second y) (first_member x) (second_member y) (interiorTime s) (interiorTime t)
    s.property.1 s.property.2 (hx.trans hy.symm)
  have parameters := injective_target same.1
  exact distinct x (same.2.2.trans (congrArg second parameters.symm))

include size small_faces in
/-- Every point in a route strip avoids both the source and the cut set. -/
theorem small_routeStrip_outside_cutSet (a : frontier P.body) {X : Type*} [TopologicalSpace X]
    (target : X → frontier P.body) (cut : ∀ x, target x ∈ P.cutSet a)
    (routes : C(X, P.BoundaryCurve)) (member : ∀ x, routes x ∈ P.geodesicFiber a (target x))
    (b : frontier P.body) (inside : b ∈ routeStrip routes) : b ≠ a ∧ b ∉ P.cutSet a := by
  obtain ⟨⟨x, t⟩, rfl⟩ := inside
  have h := member x
  have first : routes x 0 = a := congrArg Prod.fst h.2
  have last : routes x 1 = target x := congrArg Prod.snd h.2
  have different : a ≠ target x := fun same => P.source_not_cutSet a (same.symm ▸ cut x)
  constructor
  · intro same
    have equal := P.geodesicFiber_injective a (target x) different (routes x) h (same.trans first.symm)
    have real_equal := congrArg Subtype.val equal
    exact t.property.1.ne' real_equal
  · have outside := small_geodesic_proper_prefix_outside_cutSet size small_faces (routes x) h.1
      (by simpa only [first, last] using different) (interiorTime t) t.property.2
    simpa only [first] using outside

end SixVertexUnfolding.ConvexPolyhedron
