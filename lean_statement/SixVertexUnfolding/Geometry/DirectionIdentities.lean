import SixVertexUnfolding.Geometry.PlanarDirections

/-! Cartesian identities for changing the origin and angular representative in the slit coordinates. -/

namespace SixVertexUnfolding

open Real

theorem direction_add_pi (θ : ℝ) : direction (θ + π) = -direction θ := by
  ext i
  fin_cases i <;> simp [direction, cos_add_pi, sin_add_pi]

theorem direction_sub_pi (θ : ℝ) : direction (θ - π) = -direction θ := by
  ext i
  fin_cases i <;> simp [direction, cos_sub_pi, sin_sub_pi]

theorem direction_add_two_pi (θ : ℝ) : direction (θ + 2 * π) = direction θ := by
  ext i
  fin_cases i <;> simp [direction]

theorem direction_two_pi_sub (θ : ℝ) : direction (2 * π - θ) = direction (-θ) := by
  rw [show 2 * π - θ = -θ + 2 * π by ring, direction_add_two_pi]

theorem direction_pi : direction π = -direction 0 := by simpa using direction_add_pi 0

end SixVertexUnfolding
