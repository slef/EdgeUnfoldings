import SixVertexUnfolding.Geometry.LocalPlaneRigidity
import SixVertexUnfolding.Geometry.FacetCoordinateChange
import SixVertexUnfolding.Geometry.PlacedTriangle
import SixVertexUnfolding.Geometry.CofacialStarCuts

/-! A locally isometric surface development moves each uncut original
face interior by one rigid motion. The conclusion supplies a placement
of the whole original polygon, including its boundary. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- An uncut face interior determines one rigid placement of its whole face. -/
theorem uncut_face_rigid_placement {P : ConvexPolyhedron} {a : frontier P.body}
    (develop : P.UncutSurface a → Plane)
    (locally_isometric : ∀ b : P.UncutSurface a, ∃ radius > 0,
      ∀ c d : P.UncutSurface a,
        dist (c.val : Space) (b.val : Space) < radius →
        dist (d.val : Space) (b.val : Space) < radius →
        dist (develop c) (develop d) = P.surfaceDist c.val d.val)
    (F : P.Face)
    (uncut : ∀ (x : Space) (hx : x ∈ F.val),
      P.faceCoordinates F x ∈ interior (P.faceCoordinates F '' F.val) →
      (⟨x, F.subset_frontier hx⟩ : frontier P.body) ∉ P.starCuts a) :
    ∃ place : Space →ᵃ[ℝ] Plane,
      (∀ x ∈ F.val, ∀ y ∈ F.val, dist (place x) (place y) = dist x y) ∧
      ∀ b : P.UncutSurface a, (b.val : Space) ∈ F.val →
        P.faceCoordinates F b.val ∈ interior (P.faceCoordinates F '' F.val) →
        place b.val = develop b := by
  let coordinates := P.faceCoordinates F
  have coordinate_rigid := P.faceCoordinates_rigid F
  obtain ⟨lift, _, coordinate_lift, lift_coordinate, lift_rigid⟩ :=
    F.exists_rigid_plane_inverse coordinates coordinate_rigid
  let region := interior (coordinates '' F.val)
  have in_face (x : region) : lift x ∈ F.val := by
    obtain ⟨y, yF, hy⟩ := interior_subset x.property
    change coordinates y = (x : Plane) at hy
    rw [← hy, lift_coordinate y (subset_affineSpan ℝ _ yF)]
    exact yF
  let inclusion (x : region) : P.UncutSurface a :=
    ⟨⟨lift x, F.subset_frontier (in_face x)⟩,
      uncut (lift x) (in_face x) (by rw [coordinate_lift]; exact x.property)⟩
  have distances : ∀ x : region, ∃ radius > 0, ∀ y z : region,
      dist (y : Plane) x < radius → dist (z : Plane) x < radius →
      dist (develop (inclusion y)) (develop (inclusion z)) = dist (y : Plane) z := by
    intro x
    obtain ⟨radius, positive, near⟩ := locally_isometric (inclusion x)
    refine ⟨radius, positive, ?_⟩
    intro y z hy hz
    have y_near : dist ((inclusion y).val : Space) ((inclusion x).val : Space) < radius := by
      change dist (lift y) (lift x) < radius
      rwa [lift_rigid]
    have z_near : dist ((inclusion z).val : Space) ((inclusion x).val : Space) < radius := by
      change dist (lift z) (lift x) < radius
      rwa [lift_rigid]
    rw [near (inclusion y) (inclusion z) y_near z_near,
      P.surfaceDist_eq_dist_in_face F (in_face y) (in_face z)]
    exact lift_rigid y z
  obtain ⟨motion, agrees⟩ := connected_open_plane_local_isometry region isOpen_interior
    (F.placed_face_interior_nonempty coordinates coordinate_rigid)
    (F.convex.affine_image coordinates).interior.isPreconnected
    (fun x => develop (inclusion x)) distances
  refine ⟨motion.toAffineMap.comp coordinates, ?_, ?_⟩
  · intro x hx y hy
    exact (motion.isometry.dist_eq _ _).trans (coordinate_rigid x hx y hy)
  · intro b bF interior_b
    let x : region := ⟨coordinates b.val, interior_b⟩
    have returns : inclusion x = b := by
      apply Subtype.ext
      apply Subtype.ext
      exact lift_coordinate b.val (subset_affineSpan ℝ _ bF)
    change motion (coordinates b.val) = develop b
    exact (agrees x).trans (congrArg develop returns)

end SixVertexUnfolding.ConvexPolyhedron
