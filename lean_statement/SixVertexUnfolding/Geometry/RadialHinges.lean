import SixVertexUnfolding.Geometry.PlanarDirections
import SixVertexUnfolding.Geometry.HingeSideOrder

/-! Consecutive positive polar sectors unfold to opposite sides of their common radial hinge. -/

namespace SixVertexUnfolding

open Real

/-- The ordinary corner angle of a positive radial triangle is its polar-angle difference. -/
theorem radial_angle (r s α β : ℝ) (r_pos : 0 < r) (s_pos : 0 < s)
    (lower : 0 ≤ β - α) (upper : β - α ≤ π) :
    EuclideanGeometry.angle (r • direction α) (0 : Plane) (s • direction β) = β - α := by
  change InnerProductGeometry.angle (r • direction α - 0) (s • direction β - 0) = _
  simp only [sub_zero]
  rw [InnerProductGeometry.angle_smul_left_of_pos _ _ r_pos,
    InnerProductGeometry.angle_smul_right_of_pos _ _ s_pos, direction_angle α β lower upper]

theorem radial_triangle_noncollinear (r s α β : ℝ) (r_pos : 0 < r) (s_pos : 0 < s)
    (lower : 0 < β - α) (upper : β - α < π) :
    ¬ Collinear ℝ ({0, r • direction α, s • direction β} : Set Plane) := by
  have measured := radial_angle r s α β r_pos s_pos lower.le upper.le
  rw [Set.insert_comm]
  intro collinear
  rcases EuclideanGeometry.collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi.mp collinear with
    left_zero | right_zero | zero_angle | straight
  · exact (smul_ne_zero r_pos.ne' (direction_ne_zero α)) left_zero
  · exact (smul_ne_zero s_pos.ne' (direction_ne_zero β)) right_zero
  · linarith
  · linarith

/-- The transverse inner product across a radial hinge is a product of signed sines. -/
theorem radial_hinge_inner (r s t α β γ : ℝ) (s_pos : 0 < s) :
    inner ℝ (hingeSideVector 0 (s • direction β) (r • direction α))
      (hingeSideVector 0 (s • direction β) (t • direction γ)) =
        r * t * sin (α - β) * sin (γ - β) := by
  have normalized : NormedSpace.normalize (s • direction β) = direction β := by
    rw [NormedSpace.normalize_smul_of_pos s_pos,
      NormedSpace.normalize_eq_self_of_norm_eq_one (direction_norm β)]
  simp only [hingeSideVector, sub_zero, normalized]
  have components := inner_eq_hinge_components (direction_norm β) (r • direction α) (t • direction γ)
  simp only [real_inner_smul_left, inner_smul_right, direction_inner] at components
  have difference : γ - α = (γ - β) - (α - β) := by ring
  rw [difference, cos_sub] at components
  linear_combination -components

/-- Successive nondegenerate sectors lie on opposite sides of their common radial edge. -/
theorem radial_hinge_opposite (r s t α β γ : ℝ) (r_pos : 0 < r) (s_pos : 0 < s) (t_pos : 0 < t)
    (left_pos : 0 < β - α) (left_small : β - α < π)
    (right_pos : 0 < γ - β) (right_small : γ - β < π) :
    OppositeHingeSides 0 (s • direction β) (r • direction α) (t • direction γ) := by
  unfold OppositeHingeSides
  rw [radial_hinge_inner r s t α β γ s_pos]
  have left_sine : sin (α - β) < 0 := sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)
  have right_sine : 0 < sin (γ - β) := sin_pos_of_pos_of_lt_pi right_pos right_small
  exact (mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (mul_pos r_pos t_pos) left_sine) right_sine).le

end SixVertexUnfolding
