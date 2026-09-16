import SixVertexUnfolding.Geometry.FacetCoordinateChange
import SixVertexUnfolding.Geometry.OpenPlaneRigidity

/-! Rigid placements of the same original polygon differ by a planar
rigid motion. In particular, they identify the same interior points. -/

namespace SixVertexUnfolding.ConvexPolyhedron.Face

open Set

/-- Two rigid face placements differ by one planar rigid motion. -/
theorem exists_coordinate_motion {P : ConvexPolyhedron} (F : P.Face)
    (left right : Space →ᵃ[ℝ] Plane)
    (left_rigid : ∀ x ∈ F.val, ∀ y ∈ F.val, dist (left x) (left y) = dist x y)
    (right_rigid : ∀ x ∈ F.val, ∀ y ∈ F.val, dist (right x) (right y) = dist x y) :
    ∃ motion : Plane ≃ᵃⁱ[ℝ] Plane, ∀ x ∈ F.val, motion (left x) = right x := by
  obtain ⟨change_coordinates, rigid, agrees⟩ :=
    F.exists_coordinate_change left right left_rigid right_rigid
  let f : ↥(univ : Set Plane) → Plane := fun x => change_coordinates x
  obtain ⟨motion, equals⟩ := open_planar_isometry_agrees_with_motion univ isOpen_univ
    ⟨0, mem_univ _⟩ f (isometry_iff_dist_eq.mpr (fun x y => rigid x y))
  exact ⟨motion, fun x hx => (equals ⟨left x, mem_univ _⟩).trans (agrees x hx)⟩

/-- Being an interior point of a rigidly placed face is independent of the placement. -/
theorem placed_interior_iff {P : ConvexPolyhedron} (F : P.Face)
    (left right : Space →ᵃ[ℝ] Plane)
    (left_rigid : ∀ x ∈ F.val, ∀ y ∈ F.val, dist (left x) (left y) = dist x y)
    (right_rigid : ∀ x ∈ F.val, ∀ y ∈ F.val, dist (right x) (right y) = dist x y)
    {x : Space} (hx : x ∈ F.val) :
    left x ∈ interior (left '' F.val) ↔ right x ∈ interior (right '' F.val) := by
  obtain ⟨motion, agrees⟩ := F.exists_coordinate_motion left right left_rigid right_rigid
  have image : motion '' (left '' F.val) = right '' F.val := by
    rw [← image_comp]
    exact image_congr agrees
  have interiors : motion '' interior (left '' F.val) = interior (motion '' (left '' F.val)) :=
    motion.toHomeomorph.image_interior _
  rw [← image, ← interiors, ← agrees x hx]
  constructor
  · exact mem_image_of_mem motion
  · rintro ⟨y, hy, same⟩
    exact motion.injective same ▸ hy

end SixVertexUnfolding.ConvexPolyhedron.Face
