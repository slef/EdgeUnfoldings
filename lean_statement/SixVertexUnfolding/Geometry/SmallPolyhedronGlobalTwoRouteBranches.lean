import SixVertexUnfolding.Geometry.GlobalTwoRouteBranches
import SixVertexUnfolding.Geometry.SmallPolyhedronRouteFamilyCovering
import SixVertexUnfolding.Geometry.SmallPolyhedronShortestRoutes

/-! On a simply connected parameter domain, the two local shortest-route
branches extend to two globally continuous, distinct families.

Here the shortest-route inputs come from the actual vertex fans of a
polyhedron with at most six vertices and triangular/quadrilateral faces.
No canonical graph model is assumed. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

variable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include size small_faces in
/-- Both routes can be continuously labelled throughout a simply connected family of regular cut targets. -/
theorem small_continuous_two_route_branches (a : frontier P.body) {X : Type*} [TopologicalSpace X]
    [SimplyConnectedSpace X] [LocPathConnectedSpace X] (x₀ : X)
    (target : X → frontier P.body) (continuous_target : Continuous target)
    (different : ∀ x, a ≠ target x) (nonvertex : ∀ x, (target x : Space) ∉ P.vertices)
    (two : ∀ x, Nat.card (P.geodesicFiber a (target x)) = 2) :
    ∃ first second : C(X, P.BoundaryCurve), (∀ x, first x ≠ second x) ∧
      ∀ x, P.geodesicFiber a (target x) = {first x, second x} := by
  have covering := small_route_family_covering size small_faces a target continuous_target different nonvertex two
  obtain ⟨f₀, g₀, distinct₀, pair₀⟩ := ncard_eq_two.mp (two x₀)
  have f_mem : f₀ ∈ P.geodesicFiber a (target x₀) := by rw [pair₀]; simp
  have g_mem : g₀ ∈ P.geodesicFiber a (target x₀) := by rw [pair₀]; simp
  let e₀ : P.RouteFamily a target := ⟨(x₀, f₀), f_mem⟩
  let e₁ : P.RouteFamily a target := ⟨(x₀, g₀), g_mem⟩
  obtain ⟨F, first_lift, _⟩ := covering.existsUnique_continuousMap_lifts (ContinuousMap.id X) x₀ e₀ rfl
  obtain ⟨G, second_lift, _⟩ := covering.existsUnique_continuousMap_lifts (ContinuousMap.id X) x₀ e₁ rfl
  have first_target (x : X) : (F x).val.1 = x := congrFun first_lift.2 x
  have second_target (x : X) : (G x).val.1 = x := congrFun second_lift.2 x
  let first : C(X, P.BoundaryCurve) := ⟨fun x => (F x).val.2, (continuous_subtype_val.comp F.continuous).snd⟩
  let second : C(X, P.BoundaryCurve) := ⟨fun x => (G x).val.2, (continuous_subtype_val.comp G.continuous).snd⟩
  have first_member (x : X) : first x ∈ P.geodesicFiber a (target x) := by
    have member := (F x).property
    rwa [first_target] at member
  have second_member (x : X) : second x ∈ P.geodesicFiber a (target x) := by
    have member := (G x).property
    rwa [second_target] at member
  have distinct (x : X) : first x ≠ second x := by
    intro same
    have equal_at_x : F x = G x := Subtype.ext (Prod.ext ((first_target x).trans (second_target x).symm) same)
    have equal := covering.eq_of_comp_eq F.continuous G.continuous
      (first_lift.2.trans second_lift.2.symm) x equal_at_x
    have at_base := congrArg (fun H : X → P.RouteFamily a target => (H x₀).val.2) equal
    change (F x₀).val.2 = (G x₀).val.2 at at_base
    rw [first_lift.1, second_lift.1] at at_base
    exact distinct₀ at_base
  refine ⟨first, second, distinct, ?_⟩
  intro x
  apply Eq.symm
  apply eq_of_subset_of_ncard_le
  · rintro f (rfl | rfl)
    · exact first_member x
    · exact second_member x
  · have count : (P.geodesicFiber a (target x)).ncard = 2 := two x
    rw [count, ncard_pair (distinct x)]
  · exact small_geodesicFiber_finite size small_faces a (target x) (different x)

end SixVertexUnfolding.ConvexPolyhedron
