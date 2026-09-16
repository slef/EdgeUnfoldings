import SixVertexUnfolding.Geometry.TriangleMetricComparison

/-! Rigid side lengths preserve the ordinary angles of a triangle. -/

namespace SixVertexUnfolding

/-- The three distance equalities give equality of the angle at the first corner. -/
theorem triangle_angle_of_distances (a b c : Space) (A B C : Plane)
    (ab : dist A B = dist a b) (ac : dist A C = dist a c) (bc : dist B C = dist b c) :
    EuclideanGeometry.angle B A C = EuclideanGeometry.angle b a c := by
  have b_length : ‖B - A‖ = ‖b - a‖ := by simpa only [dist_eq_norm, norm_sub_rev] using ab
  have c_length : ‖C - A‖ = ‖c - a‖ := by simpa only [dist_eq_norm, norm_sub_rev] using ac
  change Real.arccos (inner ℝ (B - A) (C - A) / (‖B - A‖ * ‖C - A‖)) =
    Real.arccos (inner ℝ (b - a) (c - a) / (‖b - a‖ * ‖c - a‖))
  rw [triangle_inner_of_distances a b c A B C ab ac bc, b_length, c_length]

end SixVertexUnfolding
