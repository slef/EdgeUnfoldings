import SixVertexUnfolding.Geometry.TriangleAngles

/-! With the two radial lengths fixed, shortening the opposite chord
cannot increase the ordinary corner angle. -/

namespace SixVertexUnfolding

/-- A nonexpanding chord gives the corresponding comparison of triangle angles. -/
theorem triangle_angle_le_of_distances (a b c : Space) (A B C : Plane)
    (ab : dist A B = dist a b) (ac : dist A C = dist a c)
    (bc : dist b c ≤ dist B C) :
    EuclideanGeometry.angle b a c ≤ EuclideanGeometry.angle B A C := by
  have b_length : ‖B - A‖ = ‖b - a‖ := by simpa only [dist_eq_norm, norm_sub_rev] using ab
  have c_length : ‖C - A‖ = ‖c - a‖ := by simpa only [dist_eq_norm, norm_sub_rev] using ac
  have chord : ‖b - c‖ ^ 2 ≤ ‖B - C‖ ^ 2 := by
    simpa only [dist_eq_norm] using (sq_le_sq₀ dist_nonneg dist_nonneg).mpr bc
  have original := norm_sub_sq_real (b - a) (c - a)
  have placed := norm_sub_sq_real (B - A) (C - A)
  simp only [sub_sub_sub_cancel_right] at original placed
  rw [b_length, c_length] at placed
  have product : inner ℝ (B - A) (C - A) ≤ inner ℝ (b - a) (c - a) := by
    linarith
  change Real.arccos (inner ℝ (b - a) (c - a) / (‖b - a‖ * ‖c - a‖)) ≤
    Real.arccos (inner ℝ (B - A) (C - A) / (‖B - A‖ * ‖C - A‖))
  rw [b_length, c_length]
  exact Real.arccos_le_arccos (div_le_div_of_nonneg_right product
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)))

end SixVertexUnfolding
