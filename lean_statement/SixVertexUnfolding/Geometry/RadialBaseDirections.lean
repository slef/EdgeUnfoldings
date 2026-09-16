import SixVertexUnfolding.Geometry.PolarPointUniqueness
import SixVertexUnfolding.Geometry.DirectionIdentities

/-! Exact directions of a radial triangle's base, measured at either endpoint. -/

namespace SixVertexUnfolding

open Real EuclideanGeometry

theorem radial_base_dist_pos (r s α β : ℝ) (r_pos : 0 < r) (s_pos : 0 < s)
    (angle_pos : 0 < β - α) (angle_small : β - α < π) :
    0 < dist (r • direction α) (s • direction β) := by
  apply dist_pos.mpr
  intro same
  apply radial_triangle_noncollinear r s α β r_pos s_pos angle_pos angle_small
  simpa [same] using collinear_pair ℝ (0 : Plane) (s • direction β)

/-- At the first endpoint, the base direction is the inward radial direction minus the fan corner. -/
theorem radial_base_direction_left (r s α β : ℝ) (r_pos : 0 < r) (s_pos : 0 < s)
    (angle_pos : 0 < β - α) (angle_small : β - α < π) :
    s • direction β - r • direction α =
      dist (r • direction α) (s • direction β) •
        direction (α + π - angle 0 (r • direction α) (s • direction β)) := by
  let γ := angle 0 (r • direction α) (s • direction β)
  have noncollinear := radial_triangle_noncollinear r s α β r_pos s_pos angle_pos angle_small
  have γ_pos : 0 < γ := angle_pos_of_not_collinear noncollinear
  have γ_small : γ < π := angle_lt_pi_of_not_collinear noncollinear
  have axis : r • direction (α + π) = 0 - r • direction α := by
    rw [direction_add_pi, smul_neg]
    module
  have measured : angle (r • direction (α + π)) 0 (s • direction β - r • direction α) = γ := by
    change InnerProductGeometry.angle (r • direction (α + π) - 0) ((s • direction β - r • direction α) - 0) =
      InnerProductGeometry.angle (0 - r • direction α) (s • direction β - r • direction α)
    rw [sub_zero, sub_zero, axis]
  apply polar_point_eq_of_cos_and_side r _ (α + π) (α + π - γ) r_pos
    (radial_base_dist_pos r s α β r_pos s_pos angle_pos angle_small)
  · simp only [dist_eq_norm, zero_sub, norm_neg, norm_sub_rev]
  · rw [measured, show α + π - γ - (α + π) = -γ by ring, cos_neg]
  · rw [show α + π - γ - (α + π) = -γ by ring, sin_neg,
      det_sub_right, det_smul_right, det_smul_right, direction_det, direction_det]
    rw [show β - (α + π) = (β - α) - π by ring, show α - (α + π) = -π by ring]
    simp only [sin_sub_pi, sin_neg, sin_pi]
    have first := sin_pos_of_pos_of_lt_pi angle_pos angle_small
    have second := sin_pos_of_pos_of_lt_pi γ_pos γ_small
    nlinarith [mul_nonneg (mul_nonneg s_pos.le first.le) second.le]

/-- At the last endpoint, the base direction is the inward radial direction plus the fan corner. -/
theorem radial_base_direction_right (r s α β : ℝ) (r_pos : 0 < r) (s_pos : 0 < s)
    (angle_pos : 0 < β - α) (angle_small : β - α < π) :
    r • direction α - s • direction β =
      dist (r • direction α) (s • direction β) •
        direction (β - π + angle 0 (s • direction β) (r • direction α)) := by
  let γ := angle 0 (s • direction β) (r • direction α)
  have noncollinear : ¬ Collinear ℝ ({0, s • direction β, r • direction α} : Set Plane) := by
    have reorder : ({0, s • direction β, r • direction α} : Set Plane) = {0, r • direction α, s • direction β} := by
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [reorder]
    exact radial_triangle_noncollinear r s α β r_pos s_pos angle_pos angle_small
  have γ_pos : 0 < γ := angle_pos_of_not_collinear noncollinear
  have γ_small : γ < π := angle_lt_pi_of_not_collinear noncollinear
  have axis : s • direction (β - π) = 0 - s • direction β := by
    rw [direction_sub_pi, smul_neg]
    module
  have measured : angle (s • direction (β - π)) 0 (r • direction α - s • direction β) = γ := by
    change InnerProductGeometry.angle (s • direction (β - π) - 0) ((r • direction α - s • direction β) - 0) =
      InnerProductGeometry.angle (0 - s • direction β) (r • direction α - s • direction β)
    rw [sub_zero, sub_zero, axis]
  apply polar_point_eq_of_cos_and_side s _ (β - π) (β - π + γ) s_pos
    (radial_base_dist_pos r s α β r_pos s_pos angle_pos angle_small)
  · simp only [dist_eq_norm, zero_sub, norm_neg]
  · rw [measured, show β - π + γ - (β - π) = γ by ring]
  · rw [show β - π + γ - (β - π) = γ by ring,
      det_sub_right, det_smul_right, det_smul_right, direction_det, direction_det]
    rw [show α - (β - π) = -(β - α) + π by ring, show β - (β - π) = π by ring]
    simp only [sin_add_pi, sin_neg, sin_pi, neg_neg, mul_zero, sub_zero]
    exact mul_nonneg (mul_nonneg r_pos.le (sin_pos_of_pos_of_lt_pi angle_pos angle_small).le)
      (sin_pos_of_pos_of_lt_pi γ_pos γ_small).le

end SixVertexUnfolding
