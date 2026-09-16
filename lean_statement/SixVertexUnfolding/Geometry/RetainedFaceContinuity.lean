import SixVertexUnfolding.Geometry.UncutFaceRigidity

/-! Agreement on a face interior extends to every retained boundary
point of that face. Cut points themselves are kept outside the domain. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- Ordinary planar interior points are dense in the corresponding original face. -/
theorem Face.placed_interior_dense {P : ConvexPolyhedron} (F : P.Face)
    (place : Space →ᵃ[ℝ] Plane)
    (rigid : ∀ x ∈ F.val, ∀ y ∈ F.val, dist (place x) (place y) = dist x y) :
    Dense {x : F.val | place x ∈ interior (place '' F.val)} := by
  let f : F.val → Plane := fun x => place x
  have isometric : Isometry f := isometry_iff_dist_eq.mpr
    (fun x y => rigid x x.property y y.property)
  have image : f '' {x : F.val | place x ∈ interior (place '' F.val)} =
      interior (place '' F.val) := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hx
    · intro z hz
      obtain ⟨x, hx, rfl⟩ := interior_subset hz
      exact ⟨⟨x, hx⟩, hz, rfl⟩
  intro x
  rw [isometric.isEmbedding.closure_eq_preimage_closure_image, image,
    F.placed_face_regular place rigid]
  exact mem_image_of_mem place x.property

/-- Continuity determines the placement on every uncut edge point as well as the face interior. -/
theorem Face.agrees_on_retained_face {P : ConvexPolyhedron} {a : frontier P.body}
    (F : P.Face) (develop : C(P.UncutSurface a, Plane)) (place : Space →ᵃ[ℝ] Plane)
    (agrees : ∀ b : P.UncutSurface a, (b.val : Space) ∈ F.val →
      P.faceCoordinates F b.val ∈ interior (P.faceCoordinates F '' F.val) →
      place b.val = develop b) :
    ∀ b : P.UncutSurface a, (b.val : Space) ∈ F.val → place b.val = develop b := by
  let boundary : C(F.val, frontier P.body) :=
    ⟨fun x => ⟨x, F.subset_frontier x.property⟩, continuous_subtype_val.subtype_mk _⟩
  let retained : Set F.val := boundary ⁻¹' (P.starCuts a)ᶜ
  have open_retained : IsOpen retained := (P.starCuts_closed a).isOpen_compl.preimage boundary.continuous
  let inclusion : C(retained, P.UncutSurface a) :=
    ⟨fun x => ⟨boundary x, x.property⟩,
      (boundary.continuous.comp continuous_subtype_val).subtype_mk _⟩
  let inside : Set retained :=
    {x | P.faceCoordinates F (x.val : Space) ∈ interior (P.faceCoordinates F '' F.val)}
  have dense : Dense inside :=
    (F.placed_interior_dense (P.faceCoordinates F) (P.faceCoordinates_rigid F)).preimage
      open_retained.isOpenMap_subtype_val
  have equal_on : EqOn (fun x : retained => place (x.val : Space))
      (fun x => develop (inclusion x)) inside := by
    intro x hx
    exact agrees (inclusion x) x.val.property hx
  have equal_everywhere := equal_on.closure
    (place.continuous_of_finiteDimensional.comp
      (continuous_subtype_val.comp continuous_subtype_val))
    (develop.continuous.comp inclusion.continuous)
  intro b bF
  let x : retained := ⟨⟨b.val, bF⟩, b.property⟩
  exact equal_everywhere (dense x)

end SixVertexUnfolding.ConvexPolyhedron
