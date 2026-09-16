import SixVertexUnfolding.Geometry.FacetPlaneInverse
import SixVertexUnfolding.Geometry.FacePlacement

/-! Different rigid coordinates on one facet differ by a planar isometry.
This places all developed source copies in one common target-face plane. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- Choose fixed planar coordinates for each original whole facet. -/
noncomputable def faceCoordinates (P : ConvexPolyhedron) (F : P.Face) : Space →ᵃ[ℝ] Plane :=
  F.exists_rigid_placement.choose

theorem faceCoordinates_rigid (P : ConvexPolyhedron) (F : P.Face) :
    ∀ x ∈ F.val, ∀ y ∈ F.val, dist (P.faceCoordinates F x) (P.faceCoordinates F y) = dist x y :=
  F.exists_rigid_placement.choose_spec

/-- Two rigid placements of one facet are related by an everywhere distance-preserving affine map. -/
theorem Face.exists_coordinate_change {P : ConvexPolyhedron} (F : P.Face)
    (left right : Space →ᵃ[ℝ] Plane)
    (left_rigid : ∀ x ∈ F.val, ∀ y ∈ F.val, dist (left x) (left y) = dist x y)
    (right_rigid : ∀ x ∈ F.val, ∀ y ∈ F.val, dist (right x) (right y) = dist x y) :
    ∃ motion : Plane →ᵃ[ℝ] Plane,
      (∀ x y, dist (motion x) (motion y) = dist x y) ∧
      ∀ x ∈ F.val, motion (left x) = right x := by
  obtain ⟨lift, in_plane, _, inverse, rigid⟩ := F.exists_rigid_plane_inverse left left_rigid
  refine ⟨right.comp lift, ?_, ?_⟩
  · intro x y
    change dist (right (lift x)) (right (lift y)) = dist x y
    rw [F.rigid_on_plane right right_rigid _ (in_plane x) _ (in_plane y), rigid]
  · intro x hx
    change right (lift (left x)) = right x
    rw [inverse x (subset_affineSpan ℝ _ hx)]

end SixVertexUnfolding.ConvexPolyhedron
