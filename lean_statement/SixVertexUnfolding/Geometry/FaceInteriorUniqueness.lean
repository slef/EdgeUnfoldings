import SixVertexUnfolding.Geometry.FacetCoordinateChange
import SixVertexUnfolding.Geometry.OpenPlaneRigidity
import SixVertexUnfolding.Geometry.Intersections

/-! An interior point of a placed original face belongs to no other
original face. A supporting affine height attaining a local maximum
inside a planar disk must be constant on the whole plane. -/

namespace SixVertexUnfolding

open Set

/-- An affine height bounded above near one planar point is constant everywhere. -/
theorem affine_plane_constant_of_local_max (height : Plane →ᵃ[ℝ] ℝ)
    (center : Plane) (radius : ℝ) (positive : 0 < radius)
    (bound : ∀ x ∈ Metric.ball center radius, height x ≤ height center) :
    ∀ x, height x = height center := by
  have agrees : EqOn height (AffineMap.const ℝ Plane (height center)) (Metric.ball center radius) := by
    intro x inside
    have reflected : AffineMap.lineMap center x (-1 : ℝ) ∈ Metric.ball center radius := by
      rw [Metric.mem_ball, dist_lineMap_left]
      simpa only [norm_neg, norm_one, one_mul, dist_comm] using (Metric.mem_ball.mp inside)
    have other := bound _ reflected
    rw [AffineMap.apply_lineMap, AffineMap.lineMap_apply_module] at other
    simp only [smul_eq_mul] at other
    change height x = height center
    linarith [bound x inside]
  have same := AffineMap.ext_on
    (Metric.isOpen_ball.affineSpan_eq_top ⟨center, Metric.mem_ball_self positive⟩) agrees
  intro x
  exact congrArg (fun f : Plane →ᵃ[ℝ] ℝ => f x) same

namespace ConvexPolyhedron.Face

/-- A point in the ordinary planar interior of a rigidly placed face belongs to that face alone. -/
theorem unique_of_placed_interior {P : ConvexPolyhedron} (F G : P.Face)
    (place : Space →ᵃ[ℝ] Plane)
    (rigid : ∀ x ∈ F.val, ∀ y ∈ F.val, dist (place x) (place y) = dist x y)
    {x : Space} (xF : x ∈ F.val) (inside : place x ∈ interior (place '' F.val))
    (xG : x ∈ G.val) : F = G := by
  obtain ⟨lift, _, _, lift_place, _⟩ := F.exists_rigid_plane_inverse place rigid
  obtain ⟨_, normal, level, _, support, face_eq⟩ := G.property
  let height : Plane →ᵃ[ℝ] ℝ := (innerSL ℝ normal).toLinearMap.toAffineMap.comp lift
  have center_height : height (place x) = level := by
    change inner ℝ normal (lift (place x)) = level
    rw [lift_place x (subset_affineSpan ℝ _ xF)]
    exact (face_eq ▸ xG).2
  obtain ⟨radius, positive, disk_in⟩ := Metric.isOpen_iff.mp isOpen_interior (place x) inside
  have bound : ∀ z ∈ Metric.ball (place x) radius, height z ≤ height (place x) := by
    intro z hz
    obtain ⟨y, yF, at_z⟩ := interior_subset (disk_in hz)
    rw [center_height, ← at_z]
    change inner ℝ normal (lift (place y)) ≤ level
    rw [lift_place y (subset_affineSpan ℝ _ yF)]
    exact support y (F.subset_body yF)
  have constant := affine_plane_constant_of_local_max height (place x) radius positive bound
  apply F.eq_of_subset G
  intro y yF
  rw [face_eq]
  refine ⟨F.subset_body yF, ?_⟩
  have equal := constant (place y)
  rw [center_height] at equal
  change inner ℝ normal (lift (place y)) = level at equal
  rwa [lift_place y (subset_affineSpan ℝ _ yF)] at equal

end ConvexPolyhedron.Face
end SixVertexUnfolding
