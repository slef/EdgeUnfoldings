import SixVertexUnfolding.Geometry.RouteStripCoverage
import SixVertexUnfolding.Geometry.SmallPolyhedronCutRayCoordinates
import SixVertexUnfolding.Geometry.SmallPolyhedronCutRetraction
import SixVertexUnfolding.Geometry.SmallPolyhedronRouteStrips

/-! The two route strips cover exactly the noncut points whose terminal
ray endpoints lie in the chosen target family. This is an equality of
actual surface regions, not a combinatorial coverage assumption.

Here the shortest-route inputs come from the actual vertex fans of a
polyhedron with at most six vertices and triangular/quadrilateral faces.
No canonical graph model is assumed. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

variable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include size small_faces in
/-- The endpoint retraction sends a swept strip point to the target of its route. -/
theorem small_routeStrip_endpoint (a : frontier P.body) {X : Type*} [TopologicalSpace X]
    (target : X → frontier P.body) (cut : ∀ x, target x ∈ P.cutSet a)
    (routes : C(X, P.BoundaryCurve)) (member : ∀ x, routes x ∈ P.geodesicFiber a (target x))
    (b : frontier P.body) (different : b ≠ a) (inside : b ∈ routeStrip routes) :
    (small_cutEndpoint size small_faces a ⟨b, different⟩).val ∈ range target := by
  obtain ⟨⟨x, t⟩, at_t⟩ := inside
  obtain ⟨nonzero, endpoint⟩ := small_cutEndpoint_on_route size small_faces a (target x) (cut x)
    (routes x) (member x) (interiorTime t) t.property.1
  have same_input : (⟨routes x (interiorTime t), nonzero⟩ : {b : frontier P.body // b ≠ a}) =
      ⟨b, different⟩ := Subtype.ext at_t
  rw [same_input] at endpoint
  exact ⟨x, endpoint.symm⟩

include size small_faces in
/-- Every noncut point extending to one of the targets is reached by one of its two route branches. -/
theorem small_mem_routeStrips_of_endpoint (a : frontier P.body) {X : Type*} [TopologicalSpace X]
    (target : X → frontier P.body) (cut : ∀ x, target x ∈ P.cutSet a)
    (first second : C(X, P.BoundaryCurve))
    (pair : ∀ x, P.geodesicFiber a (target x) = {first x, second x})
    (b : frontier P.body) (different : b ≠ a) (outside : b ∉ P.cutSet a)
    (endpoint : (small_cutEndpoint size small_faces a ⟨b, different⟩).val ∈ range target) :
    b ∈ routeStrip first ∪ routeStrip second := by
  obtain ⟨x, at_x⟩ := endpoint
  have extension := small_cutEndpoint_extension size small_faces a ⟨b, different⟩
  rw [← at_x] at extension
  obtain ⟨f, hf, s, at_s⟩ := P.shortest_extension_path a b (target x) extension
  have f0 : f 0 = a := congrArg Prod.fst hf.2
  have f1 : f 1 = target x := congrArg Prod.snd hf.2
  have positive : 0 < s := lt_of_le_of_ne s.property.1 (by
    intro zero
    have equal : s = 0 := zero.symm
    rw [equal, f0] at at_s
    exact different at_s.symm)
  have before : s < 1 := lt_of_le_of_ne s.property.2 (by
    intro one
    have equal : s = 1 := one
    rw [equal, f1] at at_s
    exact outside (at_s ▸ cut x))
  let t : Ioo (0 : ℝ) 1 := ⟨s.val, positive, before⟩
  have time : interiorTime t = s := rfl
  rw [pair x] at hf
  rcases hf with rfl | rfl
  · exact Or.inl ⟨(x, t), by change first x (interiorTime t) = b; rwa [time]⟩
  · exact Or.inr ⟨(x, t), by change second x (interiorTime t) = b; rwa [time]⟩

include size small_faces in
/-- The exact radial partition over a two-route target family. -/
theorem small_routeStrips_iff_endpoint (a : frontier P.body) {X : Type*} [TopologicalSpace X]
    (target : X → frontier P.body) (cut : ∀ x, target x ∈ P.cutSet a)
    (first second : C(X, P.BoundaryCurve))
    (pair : ∀ x, P.geodesicFiber a (target x) = {first x, second x})
    (b : frontier P.body) (different : b ≠ a) :
    b ∈ routeStrip first ∪ routeStrip second ↔ b ∉ P.cutSet a ∧
      (small_cutEndpoint size small_faces a ⟨b, different⟩).val ∈ range target := by
  have first_member (x : X) : first x ∈ P.geodesicFiber a (target x) := by rw [pair x]; simp
  have second_member (x : X) : second x ∈ P.geodesicFiber a (target x) := by rw [pair x]; simp
  constructor
  · rintro (inside | inside)
    · exact ⟨(small_routeStrip_outside_cutSet size small_faces a target cut first first_member b inside).2,
        small_routeStrip_endpoint size small_faces a target cut first first_member b different inside⟩
    · exact ⟨(small_routeStrip_outside_cutSet size small_faces a target cut second second_member b inside).2,
        small_routeStrip_endpoint size small_faces a target cut second second_member b different inside⟩
  · rintro ⟨outside, endpoint⟩
    exact small_mem_routeStrips_of_endpoint size small_faces a target cut first second pair b different outside endpoint

end SixVertexUnfolding.ConvexPolyhedron
