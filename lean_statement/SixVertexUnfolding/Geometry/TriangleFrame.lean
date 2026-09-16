import SixVertexUnfolding.Geometry.PlaneOrientation
import SixVertexUnfolding.Geometry.HingeIsometries
import SixVertexUnfolding.Geometry.RadialBaseDirections

/-! A triangle has a rigid coordinate frame with its base horizontal and its apex above the base. -/

namespace SixVertexUnfolding

open Real EuclideanGeometry

/-- Dot product and signed area against one nonzero vector determine a planar vector. -/
theorem point_eq_of_inner_and_det (axis x y : Plane) (nonzero : axis ≠ 0)
    (same_inner : inner ℝ axis x = inner ℝ axis y) (same_det : det axis x = det axis y) : x = y := by
  have identity := det_sq_add_inner_sq axis (x - y)
  rw [det_sub_right, same_det, sub_self, inner_sub_right, same_inner, sub_self] at identity
  have axis_pos : 0 < ‖axis‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr nonzero)
  have difference_zero : ‖x - y‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖x - y‖]
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp difference_zero))

/-- Signed sine and cosine determine the rotated copy without choosing an angular branch. -/
theorem polar_point_eq_of_inner_det (r φ κ : ℝ) (r_pos : 0 < r) (x : Plane)
    (cosine : inner ℝ (r • direction φ) x = r ^ 2 * cos κ)
    (sine : det (r • direction φ) x = r ^ 2 * sin κ) : x = r • direction (φ + κ) := by
  apply point_eq_of_inner_and_det (r • direction φ) x _
  · apply norm_pos_iff.mp
    simp only [norm_smul, direction_norm, mul_one, Real.norm_eq_abs, abs_of_pos r_pos]
    exact r_pos
  · rw [cosine, real_inner_smul_left, inner_smul_right, direction_inner,
      show φ + κ - φ = κ by ring]
    ring
  · rw [sine, det_smul_left, det_smul_right, direction_det, show φ + κ - φ = κ by ring]
    ring

/-- This frame uses only ordinary side lengths and the left base angle of the given triangle. -/
theorem exists_upper_triangle_frame (a b m : Plane)
    (noncollinear : ¬ Collinear ℝ ({a, b, m} : Set Plane)) :
    ∃ motion : Plane ≃ᵃⁱ[ℝ] Plane, motion a = 0 ∧
      motion b = dist a b • direction 0 ∧ motion m = dist a m • direction (angle b a m) := by
  have ab : 0 < dist a b := dist_pos.mpr (ne₁₂_of_not_collinear noncollinear)
  have am : 0 < dist a m := dist_pos.mpr (ne₁₃_of_not_collinear noncollinear)
  apply exists_plane_motion_triangle a b m 0 (dist a b • direction 0)
    (dist a m • direction (angle b a m))
  · exact dist_pos.mp (by rw [polar_radius _ _ ab.le]; exact ab)
  · exact (polar_radius _ _ ab.le).symm
  · exact (polar_radius _ _ am.le).symm
  · apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
    rw [polar_distance_sq, sub_zero]
    have cosine_law := law_cos b a m
    simpa only [← sq, dist_comm b a, dist_comm m a] using cosine_law

/-- In the upper frame, the apex direction measured from the right endpoint is pi minus its right base angle. -/
theorem upper_triangle_frame_right (a b m : Plane)
    (noncollinear : ¬ Collinear ℝ ({a, b, m} : Set Plane))
    (motion : Plane ≃ᵃⁱ[ℝ] Plane) (first : motion a = 0)
    (second : motion b = dist a b • direction 0)
    (apex : motion m = dist a m • direction (angle b a m)) :
    motion m = dist a b • direction 0 + dist b m • direction (π - angle a b m) := by
  have reordered : ¬ Collinear ℝ ({b, a, m} : Set Plane) := by
    simpa only [Set.insert_comm] using noncollinear
  have φ_pos := angle_pos_of_not_collinear reordered
  have φ_small := angle_lt_pi_of_not_collinear reordered
  have at_right := motion.toAffineIsometry.angle_map a b m
  change angle (motion a) (motion b) (motion m) = angle a b m at at_right
  have right_length := motion.dist_map b m
  have base_direction := radial_base_direction_left (dist a b) (dist a m) 0 (angle b a m)
    (dist_pos.mpr (ne₁₂_of_not_collinear noncollinear))
    (dist_pos.mpr (ne₁₃_of_not_collinear noncollinear))
    (by simpa only [sub_zero] using φ_pos) (by simpa only [sub_zero] using φ_small)
  rw [← second, ← apex, ← first, at_right, right_length, zero_add] at base_direction
  rw [← second]
  exact (sub_eq_iff_eq_add.mp base_direction).trans (add_comm _ _)

end SixVertexUnfolding
