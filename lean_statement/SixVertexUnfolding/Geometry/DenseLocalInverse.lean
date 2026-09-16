import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.ContinuousMap.Basic

/-! A local right inverse is a genuine inverse if a dense set of
domain points already has unique preimages. -/

namespace SixVertexUnfolding

open Set

theorem local_inverse_of_dense_unique {X Y : Type*} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace Y] (f : C(X, Y)) (good : Set X) (dense : Dense good)
    (unique : ∀ x ∈ good, ∀ y, f x = f y → x = y)
    (region : Set Y) (open_region : IsOpen region) (inverse : C(region, X))
    (right_inverse : ∀ y : region, f (inverse y) = y.val) :
    ∀ (x : X) (inside : f x ∈ region), inverse ⟨f x, inside⟩ = x := by
  let domain := f ⁻¹' region
  have open_domain : IsOpen domain := open_region.preimage f.continuous
  let first (x : domain) : X := inverse ⟨f x.val, x.property⟩
  have continuous_first : Continuous first := inverse.continuous.comp
    ((f.continuous.comp continuous_subtype_val).subtype_mk _)
  have dense_good : Dense ((fun x : domain => x.val) ⁻¹' good) :=
    dense.preimage open_domain.isOpenMap_subtype_val
  have agrees : ((fun x : domain => x.val) ⁻¹' good) ⊆ {x | first x = x.val} := by
    intro x hx
    exact (unique x.val hx (first x) (right_inverse ⟨f x.val, x.property⟩).symm).symm
  have all (x : domain) : first x = x.val :=
    closure_minimal agrees (isClosed_eq continuous_first continuous_subtype_val) (dense_good x)
  exact fun x inside => all ⟨x, inside⟩

end SixVertexUnfolding
