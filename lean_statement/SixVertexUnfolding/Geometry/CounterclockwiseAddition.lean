import SixVertexUnfolding.Geometry.CounterclockwiseAngle
import SixVertexUnfolding.Geometry.JoinedTriangleFrontier

/-! Two positive turns below pi add without wrapping past a full turn. -/

namespace SixVertexUnfolding

open Real EuclideanGeometry

/-- A positive sine in a single closed turn lies strictly in its first half. -/
theorem positive_sine_in_one_turn (θ : ℝ) (lower : 0 ≤ θ) (upper : θ ≤ 2 * π)
    (positive : 0 < sin θ) : 0 < θ ∧ θ < π := by
  constructor
  · apply lt_of_le_of_ne lower
    intro zero
    rw [← zero, sin_zero] at positive
    exact lt_irrefl 0 positive
  · by_contra after
    have nonpositive := sin_nonpos_of_nonpos_of_neg_pi_le (show θ - 2 * π ≤ 0 by linarith)
      (show -π ≤ θ - 2 * π by linarith)
    rw [sin_sub_two_pi] at nonpositive
    linarith

/-- Positive signed area chooses the next polar ray strictly within a half turn. -/
theorem polar_representation_after_ray (r α : ℝ) (r_pos : 0 < r) (x : Plane)
    (positive : 0 < det (r • direction α) x) :
    ∃ θ, α < θ ∧ θ < α + π ∧ x = dist 0 x • direction θ := by
  have nonzero : x ≠ 0 := by intro zero; simp [zero, det] at positive
  have radius_pos : 0 < dist (0 : Plane) x := dist_pos.mpr nonzero.symm
  obtain ⟨θ, lower, upper, polar⟩ := polar_representation_in_turn α x nonzero
  rw [polar, det_smul_left, det_smul_right, direction_det] at positive
  have sine : 0 < sin (θ - α) := by
    have coefficient := mul_pos r_pos radius_pos
    nlinarith
  have bounds := positive_sine_in_one_turn (θ - α) (by linarith) (by linarith) sine
  exact ⟨θ, by linarith [bounds.1], by linarith [bounds.2], polar⟩

/-- The two ordinary positive triangle corners at a joined diagonal add to the polygon corner. -/
theorem counterclockwiseAngle_add (x y z : Plane)
    (first : 0 < det x y) (second : 0 < det y z) :
    counterclockwiseAngle x z = counterclockwiseAngle x y + counterclockwiseAngle y z := by
  have x_nonzero : x ≠ 0 := by intro zero; simp [zero, det] at first
  have x_radius : 0 < dist (0 : Plane) x := dist_pos.mpr x_nonzero.symm
  obtain ⟨α, _, _, at_x⟩ := polar_representation_in_turn 0 x x_nonzero
  obtain ⟨β, ab, ab_small, at_y⟩ := polar_representation_after_ray _ α x_radius y (by rwa [← at_x])
  have y_nonzero : y ≠ 0 := by intro zero; simp [zero, det] at second
  have y_radius : 0 < dist (0 : Plane) y := dist_pos.mpr y_nonzero.symm
  obtain ⟨γ, bc, bc_small, at_z⟩ := polar_representation_after_ray _ β y_radius z (by rwa [← at_y])
  have z_nonzero : z ≠ 0 := by intro zero; simp [zero, det] at second
  have z_radius : 0 < dist (0 : Plane) z := dist_pos.mpr z_nonzero.symm
  rw [at_x, at_y, at_z,
    counterclockwiseAngle_polar _ _ α γ x_radius z_radius (by linarith) (by linarith),
    counterclockwiseAngle_polar _ _ α β x_radius y_radius (by linarith) (by linarith [pi_pos]),
    counterclockwiseAngle_polar _ _ β γ y_radius z_radius (by linarith) (by linarith [pi_pos])]
  ring

/-- A noncollinear corner contributes a strictly positive angle, including its reflex realization. -/
theorem counterclockwiseAngle_pos_of_det_ne_zero (x y : Plane) (nonzero : det x y ≠ 0) :
    0 < counterclockwiseAngle x y := by
  unfold counterclockwiseAngle
  split_ifs with negative
  · have bound := InnerProductGeometry.angle_le_pi x y
    linarith [pi_pos]
  · have noncollinear : ¬ Collinear ℝ ({x, 0, y} : Set Plane) := by
      rw [Set.insert_comm]
      apply noncollinear_of_triangle_det_ne_zero
      simpa only [sub_zero] using nonzero
    simpa only [EuclideanGeometry.angle, vsub_eq_sub, sub_zero] using angle_pos_of_not_collinear noncollinear

end SixVertexUnfolding
