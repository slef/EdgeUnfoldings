import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.ContinuousMap.Basic

/-! Two continuous images of the same compact parameter space are
homeomorphic when they make exactly the same identifications. -/

namespace SixVertexUnfolding

open Set Topology

/-- Matching fibers produce a homeomorphism that respects every parameter value. -/
theorem equal_fibers_homeomorph {X Y Z : Type*} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [T2Space Y] [TopologicalSpace Z] [T2Space Z]
    (f : C(X, Y)) (g : C(X, Z)) (same_fibers : ∀ x y, f x = f y ↔ g x = g y) :
    ∃ H : range f ≃ₜ range g, ∀ x, H ⟨f x, mem_range_self x⟩ = ⟨g x, mem_range_self x⟩ := by
  classical
  let lift (y : range f) : X := y.property.choose
  have lift_eq (y : range f) : f (lift y) = y.val := y.property.choose_spec
  let φ (y : range f) : range g := ⟨g (lift y), mem_range_self _⟩
  have agrees (x : X) : φ ⟨f x, mem_range_self x⟩ = ⟨g x, mem_range_self x⟩ :=
    Subtype.ext ((same_fibers _ _).mp (lift_eq ⟨f x, mem_range_self x⟩))
  have injective : Function.Injective φ := by
    intro y z equal
    apply Subtype.ext
    have equal_g : g (lift y) = g (lift z) := congrArg Subtype.val equal
    simpa only [lift_eq] using (same_fibers _ _).mpr equal_g
  have surjective : Function.Surjective φ := by
    rintro ⟨_, ⟨x, rfl⟩⟩
    exact ⟨⟨f x, mem_range_self x⟩, agrees x⟩
  let f' : X → range f := fun x => ⟨f x, mem_range_self x⟩
  have onto_f' : Function.Surjective f' := by
    rintro ⟨_, ⟨x, rfl⟩⟩
    exact ⟨x, rfl⟩
  have quotient : IsQuotientMap f' := IsQuotientMap.of_surjective_continuous onto_f'
    (f.continuous.subtype_mk _)
  have continuous_φ : Continuous φ := by
    apply quotient.continuous_iff.mpr
    have equal : φ ∘ f' = fun x => (⟨g x, mem_range_self x⟩ : range g) := funext agrees
    rw [equal]
    exact g.continuous.subtype_mk _
  letI : CompactSpace (range f) := isCompact_iff_compactSpace.mp (isCompact_range f.continuous)
  let H := (Equiv.ofBijective φ ⟨injective, surjective⟩).toHomeomorphOfContinuousClosed continuous_φ
    continuous_φ.isClosedMap
  exact ⟨H, agrees⟩

end SixVertexUnfolding
