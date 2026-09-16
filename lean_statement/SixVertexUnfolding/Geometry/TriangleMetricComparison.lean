import SixVertexUnfolding.Geometry.HingeStrictness
import SixVertexUnfolding.Geometry.HingeSides

/-! Apply the hinge comparison using the five original side lengths of two triangles. -/

namespace SixVertexUnfolding

/-- Three matching side lengths fix the inner product at the chosen triangle corner. -/
theorem triangle_inner_of_distances (a b x : Space) (A B X : Plane)
    (ab : dist A B = dist a b) (ax : dist A X = dist a x) (bx : dist B X = dist b x) :
    inner ℝ (B - A) (X - A) = inner ℝ (b - a) (x - a) := by
  have b_length : ‖B - A‖ = ‖b - a‖ := by simpa only [dist_eq_norm, norm_sub_rev] using ab
  have x_length : ‖X - A‖ = ‖x - a‖ := by simpa only [dist_eq_norm, norm_sub_rev] using ax
  have bx_length : ‖B - X‖ = ‖b - x‖ := by simpa only [dist_eq_norm] using bx
  have original := norm_sub_sq_real (b - a) (x - a)
  have placed := norm_sub_sq_real (B - A) (X - A)
  simp only [sub_sub_sub_cancel_right] at original placed
  rw [b_length, x_length, bx_length] at placed
  linarith

theorem triangle_hinge_component_of_distances (a b x : Space) (A B X : Plane)
    (ab : dist A B = dist a b) (ax : dist A X = dist a x) (bx : dist B X = dist b x) :
    inner ℝ (NormedSpace.normalize (B - A)) (X - A) =
      inner ℝ (NormedSpace.normalize (b - a)) (x - a) := by
  have length : ‖B - A‖ = ‖b - a‖ := by simpa only [dist_eq_norm, norm_sub_rev] using ab
  simp only [NormedSpace.normalize, real_inner_smul_left, length,
    triangle_inner_of_distances a b x A B X ab ax bx]

/-- Flattening the two triangles across their shared edge increases the free-vertex distance. -/
theorem two_triangles_distance_ge (a b x y : Space) (A B X Y : Plane) (distinct : a ≠ b)
    (ab : dist A B = dist a b)
    (ax : dist A X = dist a x) (bx : dist B X = dist b x)
    (ay : dist A Y = dist a y) (by_ : dist B Y = dist b y)
    (opposite : OppositeHingeSides A B X Y) : dist x y ≤ dist X Y := by
  have AB : A ≠ B := by intro same; have := ab; simp [same] at this; exact distinct this
  have bound := opposite_flattening_distance_ge
    (NormedSpace.normalize (b - a)) (NormedSpace.normalize (B - A))
    (NormedSpace.norm_normalize (sub_ne_zero.mpr distinct.symm))
    (NormedSpace.norm_normalize (sub_ne_zero.mpr AB.symm))
    (x - a) (y - a) (X - A) (Y - A)
    (by simpa only [dist_eq_norm, norm_sub_rev] using ax)
    (by simpa only [dist_eq_norm, norm_sub_rev] using ay)
    (triangle_hinge_component_of_distances a b x A B X ab ax bx)
    (triangle_hinge_component_of_distances a b y A B Y ab ay by_)
    opposite
  simpa only [dist_sub_right] using bound

end SixVertexUnfolding
