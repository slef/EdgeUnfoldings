import SixVertexUnfolding.Definitions

/-! On a polygon equal to the closure of its interior, agreement of
continuous maps on interior points extends across any open neighborhood. -/

namespace SixVertexUnfolding

open Set

/-- Interior points are dense in a regular closed planar region, with its relative topology. -/
theorem regular_region_interior_dense (region : Set Plane)
    (regular : closure (interior region) = region) :
    Dense {x : region | (x : Plane) ∈ interior region} := by
  have image : Subtype.val '' {x : region | (x : Plane) ∈ interior region} = interior region := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩; exact hx
    · intro x hx; exact ⟨⟨x, interior_subset hx⟩, hx, rfl⟩
  intro x
  rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image, image, regular]
  exact x.property

/-- Interior agreement extends to the boundary wherever the second map has an open domain. -/
theorem regular_patch_agreement {X : Type*} [TopologicalSpace X] [T2Space X]
    (region : Set Plane) (regular : closure (interior region) = region)
    (f : C(region, X)) (U : Set Plane) (open_U : IsOpen U) (g : C(U, X))
    (agrees : ∀ x : region, (x : Plane) ∈ interior region →
      ∀ inside : (x : Plane) ∈ U, f x = g ⟨x, inside⟩) :
    ∀ (x : region) (inside : (x : Plane) ∈ U), f x = g ⟨x, inside⟩ := by
  let domain : Set region := Subtype.val ⁻¹' U
  have open_domain : IsOpen domain := open_U.preimage continuous_subtype_val
  let first : C(domain, X) := ⟨fun x => f x.val, f.continuous.comp continuous_subtype_val⟩
  let second : C(domain, X) := ⟨fun x => g ⟨x.val, x.property⟩,
    g.continuous.comp ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)⟩
  have dense : Dense {x : domain | (x.val : Plane) ∈ interior region} :=
    (regular_region_interior_dense region regular).preimage open_domain.isOpenMap_subtype_val
  have equal_on : EqOn first second {x : domain | (x.val : Plane) ∈ interior region} :=
    fun x hx => agrees x.val hx x.property
  intro x inside
  exact equal_on.closure first.continuous second.continuous (dense ⟨x, inside⟩)

end SixVertexUnfolding
