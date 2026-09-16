import SixVertexUnfolding.Geometry.GeodesicFibers

/-! When the two shortest routes stay in disjoint neighborhoods, each
route varies continuously. Compactness rules out any jump of the selection. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- A consistently separated choice from a two-route fiber is continuous in its target. -/
theorem separated_route_selection_continuous (P : ConvexPolyhedron) (a : frontier P.body)
    {X : Type*} [TopologicalSpace X] (target : X → frontier P.body) (continuous_target : Continuous target)
    (first second : X → P.BoundaryCurve)
    (pair : ∀ x, P.geodesicFiber a (target x) = {first x, second x})
    (U W : Set P.BoundaryCurve) (openW : IsOpen W) (apart : Disjoint U W)
    (first_in : ∀ x, first x ∈ U) (second_in : ∀ x, second x ∈ W) : Continuous first := by
  apply continuous_def.mpr
  intro O openO
  apply isOpen_iff_forall_mem_open.mpr
  intro x hx
  obtain ⟨N, openN, at_x, near⟩ := P.geodesic_family_upper_continuous (a, target x) (O ∪ W)
    (openO.union openW) (by
      intro f geodesic ends
      have member : f ∈ P.geodesicFiber a (target x) := ⟨geodesic, ends⟩
      rw [pair x] at member
      rcases member with rfl | rfl
      · exact Or.inl hx
      · exact Or.inr (second_in x))
  let V : Set X := (fun y => (a, target y)) ⁻¹' N
  refine ⟨V, ?_, openN.preimage (continuous_const.prodMk continuous_target), at_x⟩
  intro y hy
  have member : first y ∈ P.geodesicFiber a (target y) := by rw [pair y]; simp
  rcases near (first y) member.1 (member.2 ▸ hy) with wanted | wrong
  · exact wanted
  · exact False.elim (disjoint_left.mp apart (first_in y) wrong)

end SixVertexUnfolding.ConvexPolyhedron
