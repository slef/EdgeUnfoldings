import SixVertexUnfolding.Geometry.CutRayCoordinates

/-! The interiors swept out by continuously varying shortest routes.
These are actual surface regions, parametrized by a target and a time
strictly between the source and the cut endpoint. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set BoundedContinuousFunction

/-- Regard a time strictly between zero and one as a closed-unit-interval time. -/
def interiorTime (t : Ioo (0 : ℝ) 1) : unitInterval := ⟨t.val, t.property.1.le, t.property.2.le⟩

theorem interiorTime_continuous : Continuous interiorTime := continuous_subtype_val.subtype_mk _

/-- Evaluate a continuous route family at an interior time. -/
noncomputable def routeStripMap {P : ConvexPolyhedron} {X : Type*} [TopologicalSpace X]
    (routes : C(X, P.BoundaryCurve)) : C(X × Ioo (0 : ℝ) 1, frontier P.body) :=
  ⟨fun p => routes p.1 (interiorTime p.2), continuous_eval.comp
    ((routes.continuous.comp continuous_fst).prodMk (interiorTime_continuous.comp continuous_snd))⟩

/-- The actual points swept out before reaching the terminal cut targets. -/
def routeStrip {P : ConvexPolyhedron} {X : Type*} [TopologicalSpace X]
    (routes : C(X, P.BoundaryCurve)) : Set (frontier P.body) := range (routeStripMap routes)

namespace SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- A strip parametrized by distinct cut endpoints has no self-identifications. -/
theorem routeStripMap_injective (a : frontier P.body) {X : Type*} [TopologicalSpace X]
    (target : X → frontier P.body) (injective_target : Function.Injective target)
    (cut : ∀ x, target x ∈ P.cutSet a) (routes : C(X, P.BoundaryCurve))
    (member : ∀ x, routes x ∈ P.geodesicFiber a (target x)) :
    Function.Injective (routeStripMap routes) := by
  rintro ⟨x, s⟩ ⟨y, t⟩ meet
  have same := graph.cut_rays_meeting small_faces a (target x) (target y) (cut x) (cut y)
    (routes x) (routes y) (member x) (member y) (interiorTime s) (interiorTime t)
    s.property.1 s.property.2 meet
  have times : s.val = t.val := congrArg (fun r : unitInterval => (r : ℝ)) same.2.1
  exact Prod.ext (injective_target same.1) (Subtype.ext times)

include graph small_faces in
/-- Two distinct route branches over the same cut-edge targets sweep disjoint interiors. -/
theorem routeStrips_disjoint (a : frontier P.body) {X : Type*} [TopologicalSpace X]
    (target : X → frontier P.body) (injective_target : Function.Injective target)
    (cut : ∀ x, target x ∈ P.cutSet a) (first second : C(X, P.BoundaryCurve))
    (first_member : ∀ x, first x ∈ P.geodesicFiber a (target x))
    (second_member : ∀ x, second x ∈ P.geodesicFiber a (target x))
    (distinct : ∀ x, first x ≠ second x) : Disjoint (routeStrip first) (routeStrip second) := by
  apply disjoint_left.mpr
  rintro b ⟨⟨x, s⟩, hx⟩ ⟨⟨y, t⟩, hy⟩
  have same := graph.cut_rays_meeting small_faces a (target x) (target y) (cut x) (cut y)
    (first x) (second y) (first_member x) (second_member y) (interiorTime s) (interiorTime t)
    s.property.1 s.property.2 (hx.trans hy.symm)
  have parameters := injective_target same.1
  exact distinct x (same.2.2.trans (congrArg second parameters.symm))

include graph small_faces in
/-- Every point in a route strip avoids both the source and the cut set. -/
theorem routeStrip_outside_cutSet (a : frontier P.body) {X : Type*} [TopologicalSpace X]
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
  · have outside := graph.geodesic_proper_prefix_outside_cutSet small_faces (routes x) h.1
      (by simpa only [first, last] using different) (interiorTime t) t.property.2
    simpa only [first] using outside

end SixVertexGraph
end SixVertexUnfolding.ConvexPolyhedron
