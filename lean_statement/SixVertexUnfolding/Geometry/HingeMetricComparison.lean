import SixVertexUnfolding.Geometry.HingeCoordinates

/-!
Flattening two triangles to opposite sides of their common hinge increases
the distance between their free vertices. The proof is Cauchy–Schwarz on
the perpendicular remainders; it does not assume an unfolding theorem.
-/

namespace SixVertexUnfolding

/-- Matching a vector's length and hinge component also matches its perpendicular length. -/
theorem hingeRemainder_norm_eq (axis : Space) (flat_axis : Plane)
    (axis_unit : ‖axis‖ = 1) (flat_unit : ‖flat_axis‖ = 1)
    (x : Space) (flat_x : Plane) (length : ‖flat_x‖ = ‖x‖)
    (along : inner ℝ flat_axis flat_x = inner ℝ axis x) :
    ‖hingeRemainder flat_axis flat_x‖ = ‖hingeRemainder axis x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [hingeRemainder_norm_sq flat_unit, hingeRemainder_norm_sq axis_unit, length, along]

/-- Opposite-side flattening minimizes the inner product of the two free-vertex vectors. -/
theorem opposite_flattening_inner_le (axis : Space) (flat_axis : Plane)
    (axis_unit : ‖axis‖ = 1) (flat_unit : ‖flat_axis‖ = 1)
    (x y : Space) (flat_x flat_y : Plane)
    (x_length : ‖flat_x‖ = ‖x‖) (y_length : ‖flat_y‖ = ‖y‖)
    (x_along : inner ℝ flat_axis flat_x = inner ℝ axis x)
    (y_along : inner ℝ flat_axis flat_y = inner ℝ axis y)
    (opposite : inner ℝ (hingeRemainder flat_axis flat_x)
      (hingeRemainder flat_axis flat_y) ≤ 0) :
    inner ℝ flat_x flat_y ≤ inner ℝ x y := by
  have flat_nonzero : flat_axis ≠ 0 := by intro zero; simp [zero] at flat_unit
  have minimum := opposite_perpendicular_inner flat_axis
    (hingeRemainder flat_axis flat_x) (hingeRemainder flat_axis flat_y) flat_nonzero
    (hingeRemainder_orthogonal flat_unit flat_x) (hingeRemainder_orthogonal flat_unit flat_y)
    opposite
  have x_remainder := hingeRemainder_norm_eq axis flat_axis axis_unit flat_unit x flat_x
    x_length x_along
  have y_remainder := hingeRemainder_norm_eq axis flat_axis axis_unit flat_unit y flat_y
    y_length y_along
  have lower := (abs_le.mp (abs_real_inner_le_norm
    (hingeRemainder axis x) (hingeRemainder axis y))).1
  rw [inner_eq_hinge_components flat_unit, inner_eq_hinge_components axis_unit,
    x_along, y_along, minimum, x_remainder, y_remainder]
  linarith

/-- The free vertices get no closer when the two triangles are flattened to opposite sides. -/
theorem opposite_flattening_distance_ge (axis : Space) (flat_axis : Plane)
    (axis_unit : ‖axis‖ = 1) (flat_unit : ‖flat_axis‖ = 1)
    (x y : Space) (flat_x flat_y : Plane)
    (x_length : ‖flat_x‖ = ‖x‖) (y_length : ‖flat_y‖ = ‖y‖)
    (x_along : inner ℝ flat_axis flat_x = inner ℝ axis x)
    (y_along : inner ℝ flat_axis flat_y = inner ℝ axis y)
    (opposite : inner ℝ (hingeRemainder flat_axis flat_x)
      (hingeRemainder flat_axis flat_y) ≤ 0) :
    dist x y ≤ dist flat_x flat_y := by
  have inner_bound := opposite_flattening_inner_le axis flat_axis axis_unit flat_unit
    x y flat_x flat_y x_length y_length x_along y_along opposite
  rw [dist_eq_norm, dist_eq_norm]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sub_sq_real, norm_sub_sq_real, x_length, y_length]
  linarith

end SixVertexUnfolding
