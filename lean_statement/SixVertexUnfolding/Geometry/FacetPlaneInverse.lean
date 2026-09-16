import SixVertexUnfolding.Geometry.PlacementRigidity
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! A rigid affine placement of a facet has an affine inverse on its entire
plane. This supplies actual inverse charts for local surface developments. -/

namespace SixVertexUnfolding.ConvexPolyhedron.Face

open Set

variable {P : ConvexPolyhedron} (F : P.Face)

/-- Rigidity on a polygon extends to its complete affine plane. -/
theorem rigid_on_plane (place : Space →ᵃ[ℝ] Plane)
    (rigid : ∀ x ∈ F.val, ∀ y ∈ F.val, dist (place x) (place y) = dist x y) :
    ∀ x ∈ affineSpan ℝ F.val, ∀ y ∈ affineSpan ℝ F.val,
      dist (place x) (place y) = dist x y :=
  affine_rigid_on_span_of_distances place F.val F.nonempty rigid

/-- Every rigid facet placement has a rigid affine lift from the Euclidean plane. -/
theorem exists_rigid_plane_inverse (place : Space →ᵃ[ℝ] Plane)
    (rigid : ∀ x ∈ F.val, ∀ y ∈ F.val, dist (place x) (place y) = dist x y) :
    ∃ lift : Plane →ᵃ[ℝ] Space,
      (∀ z, lift z ∈ affineSpan ℝ F.val) ∧
      (∀ z, place (lift z) = z) ∧
      (∀ x ∈ affineSpan ℝ F.val, lift (place x) = x) ∧
      (∀ z w, dist (lift z) (lift w) = dist z w) := by
  obtain ⟨a, aF⟩ := F.nonempty
  have a_plane := subset_affineSpan ℝ F.val aF
  let D := (affineSpan ℝ F.val).direction
  let L : D →ₗ[ℝ] Plane := place.linear.comp D.subtype
  have shifted (v : D) : (v : Space) + a ∈ affineSpan ℝ F.val :=
    AffineSubspace.vadd_mem_of_mem_direction v.property a_plane
  have value (v : D) : place ((v : Space) + a) = L v + place a := by
    have difference := place.linearMap_vsub ((v : Space) + a) a
    change place.linear (((v : Space) + a) - a) = place ((v : Space) + a) - place a at difference
    simpa only [add_sub_cancel_right, L, LinearMap.comp_apply, Submodule.subtype_apply]
      using (eq_add_of_sub_eq difference.symm)
  have injective : Function.Injective L := by
    intro v w same
    have distance := F.rigid_on_plane place rigid _ (shifted v) _ (shifted w)
    rw [value v, value w, same, dist_self] at distance
    exact Subtype.ext (add_right_cancel (dist_eq_zero.mp distance.symm))
  have dimension : Module.finrank ℝ D = Module.finrank ℝ Plane := by
    rw [show Module.finrank ℝ D = 2 from F.property.1]
    simp [Plane]
  let inverse := (L.linearEquivOfInjective injective dimension).symm
  let unshift : Plane →ᵃ[ℝ] Plane := (AffineEquiv.vaddConst ℝ (-place a)).toAffineMap
  let lift : Plane →ᵃ[ℝ] Space :=
    ((D.subtype.comp inverse.toLinearMap).toAffineMap.comp unshift) + AffineMap.const ℝ Plane a
  have formula (z : Plane) : lift z = (inverse (z - place a) : Space) + a := by
    simp [lift, unshift, sub_eq_add_neg]
  have in_plane (z : Plane) : lift z ∈ affineSpan ℝ F.val := by
    rw [formula]; exact shifted _
  have right_inverse (z : Plane) : place (lift z) = z := by
    rw [formula, value]
    have cancel : L (inverse (z - place a)) = z - place a :=
      (L.linearEquivOfInjective injective dimension).apply_symm_apply _
    rw [cancel, sub_add_cancel]
  refine ⟨lift, in_plane, right_inverse, ?_, ?_⟩
  · intro x hx
    apply dist_eq_zero.mp
    rw [← F.rigid_on_plane place rigid _ (in_plane (place x)) _ hx, right_inverse, dist_self]
  · intro z w
    rw [← F.rigid_on_plane place rigid _ (in_plane z) _ (in_plane w), right_inverse, right_inverse]

end SixVertexUnfolding.ConvexPolyhedron.Face
