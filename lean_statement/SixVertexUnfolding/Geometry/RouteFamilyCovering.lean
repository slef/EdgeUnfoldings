import SixVertexUnfolding.Geometry.TwoRouteCharts
import SixVertexUnfolding.Geometry.TwoGraphsHomeomorph

/-! Over any continuously parametrized family of regular cut targets,
the actual shortest routes form a covering with two sheets. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- A target parameter together with one of its actual normalized shortest routes. -/
abbrev RouteFamily (P : ConvexPolyhedron) (a : frontier P.body) {X : Type*}
    (target : X → frontier P.body) :=
  {p : X × P.BoundaryCurve // p.2 ∈ P.geodesicFiber a (target p.1)}

/-- Forget the chosen route and retain its target parameter. -/
def routeProjection (P : ConvexPolyhedron) (a : frontier P.body) {X : Type*}
    (target : X → frontier P.body) : P.RouteFamily a target → X := fun p => p.val.1

theorem routeProjection_continuous (P : ConvexPolyhedron) (a : frontier P.body) {X : Type*}
    [TopologicalSpace X] (target : X → frontier P.body) : Continuous (P.routeProjection a target) :=
  continuous_subtype_val.fst

namespace SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- The actual two-route family over regular targets is a topological covering. -/
theorem route_family_covering (a : frontier P.body) {X : Type*} [TopologicalSpace X]
    (target : X → frontier P.body) (continuous_target : Continuous target)
    (different : ∀ x, a ≠ target x) (nonvertex : ∀ x, (target x : Space) ∉ P.vertices)
    (two : ∀ x, Nat.card (P.geodesicFiber a (target x)) = 2) :
    IsCoveringMap (P.routeProjection a target) := by
  intro x
  obtain ⟨chart, at_x⟩ := graph.exists_two_route_chart small_faces a (target x)
    (different x) (nonvertex x) (two x)
  let V : Set X := target ⁻¹' chart.domain
  have openV : IsOpen V := chart.open_domain.preimage continuous_target
  let input (y : V) : P.twoRouteTargets a chart.domain := ⟨target y.val, y.property, two y.val⟩
  have continuous_input : Continuous input :=
    (continuous_target.comp continuous_subtype_val).subtype_mk _
  let f : V → P.BoundaryCurve := chart.first ∘ input
  let g : V → P.BoundaryCurve := chart.second ∘ input
  have continuous_f : Continuous f := chart.continuous_first.comp continuous_input
  have continuous_g : Continuous g := chart.continuous_second.comp continuous_input
  have distinct (y : V) : f y ≠ g y := chart.different (input y)
  have pair (y : V) : P.geodesicFiber a (target y.val) = {f y, g y} := chart.fiber_eq (input y)
  let unpack : (P.routeProjection a target ⁻¹' V) ≃ₜ twoGraphs f g := {
    toFun := fun e => ⟨(⟨e.val.val.1, e.property⟩, e.val.val.2), by
      change e.val.val.2 ∈ ({f ⟨e.val.val.1, e.property⟩, g ⟨e.val.val.1, e.property⟩} : Set P.BoundaryCurve)
      rw [← pair ⟨e.val.val.1, e.property⟩]
      exact e.val.property⟩
    invFun := fun e => ⟨⟨(e.val.1.val, e.val.2), by
      rw [pair e.val.1]
      exact e.property⟩, e.val.1.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  have covered : IsEvenlyCovered (P.routeProjection a target) x Bool := by
    refine ⟨inferInstance, V, at_x, openV, openV.preimage (P.routeProjection_continuous a target),
      unpack.trans (twoGraphsHomeomorph f g continuous_f continuous_g distinct), ?_⟩
    intro e
    rfl
  exact covered.to_isEvenlyCovered_preimage

end SixVertexGraph
end SixVertexUnfolding.ConvexPolyhedron
