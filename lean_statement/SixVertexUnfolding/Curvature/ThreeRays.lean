import SixVertexUnfolding.Definitions
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality

/-! A strict angle bound for three rays not contained in one plane. -/

namespace SixVertexUnfolding

open InnerProductGeometry

/-- A plane through the first two rays, excluding the third, makes the total angle less than 2π. -/
theorem three_ray_angle_sum_lt_two_pi (x y z normal : Space)
    (x_plane : inner ℝ normal x = 0) (y_plane : inner ℝ normal y = 0)
    (z_outside : inner ℝ normal z ≠ 0) (not_straight : angle x y < Real.pi) :
    angle x y + angle y z + angle z x < 2 * Real.pi := by
  have neg_z_ne : -z ≠ 0 := by
    intro zero
    have z_zero : z = 0 := neg_eq_zero.mp zero
    exact z_outside (by rw [z_zero, inner_zero_right])
  have strict : angle x y < angle x (-z) + angle (-z) y := by
    apply lt_of_le_of_ne (angle_le_angle_add_angle x (-z) y)
    intro same
    rcases (angle_eq_angle_add_angle_iff neg_z_ne).mp same with straight | in_plane
    · exact not_straight.ne straight
    · obtain ⟨a, b, combination⟩ := Submodule.mem_span_pair.mp in_plane
      change (a : ℝ) • x + (b : ℝ) • y = -z at combination
      have measured := congrArg (fun v => inner ℝ normal v) combination
      simp only [inner_add_right, inner_smul_right, inner_neg_right,
        x_plane, y_plane, mul_zero, zero_add] at measured
      exact z_outside (by linarith)
  rw [angle_neg_right, angle_neg_left] at strict
  linarith [angle_comm x z, angle_comm y z]

end SixVertexUnfolding
