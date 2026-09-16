import SixVertexUnfolding.Geometry.SourceBisectors
import SixVertexUnfolding.Geometry.HingeIsometries
import SixVertexUnfolding.Geometry.TriangleTopology

/-! Three noncollinear distance anchors determine a planar point. Hence
an isometry on a region containing a triangle is one rigid planar motion. -/

namespace SixVertexUnfolding

open Set

/-- Equal distances to three noncollinear anchors determine the point uniquely. -/
theorem plane_point_eq_of_three_distances (a b c x y : Plane)
    (noncollinear : ¬ Collinear ℝ ({a, b, c} : Set Plane))
    (at_a : dist x a = dist y a) (at_b : dist x b = dist y b) (at_c : dist x c = dist y c) : x = y := by
  let height : Plane →ᵃ[ℝ] ℝ := (innerSL ℝ (y - x)).toLinearMap.toAffineMap
  let level : Plane →ᵃ[ℝ] ℝ := AffineMap.const ℝ Plane ((‖y‖ ^ 2 - ‖x‖ ^ 2) / 2)
  have anchors : EqOn height level ({a, b, c} : Set Plane) := by
    rintro z (rfl | rfl | rfl)
    · exact (equal_site_distances_iff_bisector x y _).mp at_a
    · exact (equal_site_distances_iff_bisector x y _).mp at_b
    · exact (equal_site_distances_iff_bisector x y _).mp at_c
  have at_x := AffineMap.eqOn_affineSpan anchors (show x ∈ affineSpan ℝ ({a, b, c} : Set Plane) by
    rw [planar_triangle_spans a b c noncollinear]; trivial)
  have equal := (equal_site_distances_iff_bisector x y x).mpr at_x
  rw [dist_self] at equal
  exact (dist_eq_zero.mp equal.symm).symm

/-- An isometry on a planar region containing a triangle is the restriction of a rigid motion. -/
theorem planar_isometry_agrees_with_motion (region : Set Plane) (f : region → Plane) (isometric : Isometry f)
    (a b c : region) (noncollinear : ¬ Collinear ℝ ({(a : Plane), (b : Plane), (c : Plane)} : Set Plane)) :
    ∃ motion : Plane ≃ᵃⁱ[ℝ] Plane, ∀ x : region, motion x = f x := by
  have different : (a : Plane) ≠ b := ne₁₂_of_not_collinear noncollinear
  have images_different : f a ≠ f b := fun same => different (congrArg Subtype.val (isometric.injective same))
  obtain ⟨motion, at_a, at_b, at_c⟩ := exists_plane_motion_triangle a b c (f a) (f b) (f c)
    images_different (isometric.dist_eq a b).symm (isometric.dist_eq a c).symm (isometric.dist_eq b c).symm
  refine ⟨motion, ?_⟩
  intro x
  have same : motion.symm (f x) = (x : Plane) := by
    apply plane_point_eq_of_three_distances a b c _ _ noncollinear
    · rw [← motion.dist_map, motion.apply_symm_apply, at_a]
      exact isometric.dist_eq x a
    · rw [← motion.dist_map, motion.apply_symm_apply, at_b]
      exact isometric.dist_eq x b
    · rw [← motion.dist_map, motion.apply_symm_apply, at_c]
      exact isometric.dist_eq x c
  simpa only [motion.apply_symm_apply] using (congrArg motion same).symm

end SixVertexUnfolding
