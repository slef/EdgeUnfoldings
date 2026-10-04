import SixVertexUnfolding.Geometry.FanPolarFrames
import SixVertexUnfolding.Geometry.TriangleFrame

/-! Two outward vertex fans, attached to the same triangular cap, have one
common polar frame. This is the lower view of the prism fallback. -/

namespace SixVertexUnfolding

open Real EuclideanGeometry

/-- The left fan runs clockwise from the cap apex through its horizontal base. -/
noncomputable def ThreeTriangleChain.capDirections (left : ThreeTriangleChain) : Fin 4 → ℝ :=
  ![left.corner 0, 0, -left.corner 1, -left.corner 1 - left.corner 2]

/-- The right fan runs counterclockwise from the cap apex through the reversed base. -/
noncomputable def FourTriangleChain.capDirections (right : FourTriangleChain) : Fin 5 → ℝ :=
  ![π - right.corner 0, π, π + right.corner 1,
    π + right.corner 1 + right.corner 2, π + right.corner 1 + right.corner 2 + right.corner 3]

/-- These coordinates are consequences of the actual outward hinges and common cap. -/
theorem exists_two_fan_cap_frame (left : ThreeTriangleChain) (right : FourTriangleChain)
    (right_center : right.center = left.ray 1)
    (common_apex : right.ray 0 = left.ray 0) (left_center : right.ray 1 = left.center) :
    ∃ motion : Plane ≃ᵃⁱ[ℝ] Plane,
      motion left.center = 0 ∧ motion right.center = left.radius 1 • direction 0 ∧
      (∀ i, motion (left.ray i) - motion left.center =
        left.radius i • direction (left.capDirections i)) ∧
      (∀ i, motion (right.ray i) - motion right.center =
        right.radius i • direction (right.capDirections i)) := by
  have noncollinear : ¬ Collinear ℝ ({left.center, left.ray 1, left.ray 0} : Set Plane) := by
    simpa only [Set.pair_comm] using left.noncollinear 0
  obtain ⟨motion, first, second, apex⟩ :=
    exists_upper_triangle_frame left.center (left.ray 1) (left.ray 0) noncollinear
  have right_apex := upper_triangle_frame_right left.center (left.ray 1) (left.ray 0)
    noncollinear motion first second apex
  have left_angle : angle (left.ray 1) left.center (left.ray 0) = left.corner 0 := angle_comm _ _ _
  have right_angle : angle left.center (left.ray 1) (left.ray 0) = right.corner 0 := by
    change angle left.center (left.ray 1) (left.ray 0) =
      angle (right.ray 0) right.center (right.ray 1)
    rw [right_center, common_apex, left_center, angle_comm]
  rw [left_angle] at apex
  rw [right_angle] at right_apex
  refine ⟨motion, first, ?_, ?_, ?_⟩
  · rw [right_center]; exact second
  · apply left.polar_motion_down motion left.capDirections
    · intro i; fin_cases i <;> simp [ThreeTriangleChain.capDirections]
    · simpa only [first, sub_zero, ThreeTriangleChain.capDirections, Matrix.cons_val_zero] using apex
    · simpa only [first, sub_zero, ThreeTriangleChain.capDirections, Matrix.cons_val_one,
        Matrix.cons_val_zero] using second
  · apply right.polar_motion_up motion right.capDirections
    · intro i; fin_cases i <;> simp [FourTriangleChain.capDirections]
    · change motion (right.ray 0) - motion right.center =
        dist right.center (right.ray 0) • direction (π - right.corner 0)
      rw [right_center, common_apex, second, right_apex, add_sub_cancel_left]
    · change motion (right.ray 1) - motion right.center =
        dist right.center (right.ray 1) • direction π
      rw [left_center, right_center, first, second, zero_sub, dist_comm]
      have opposite : direction π = -direction 0 := by
        ext i; fin_cases i <;> simp [direction]
      rw [opposite, smul_neg]

end SixVertexUnfolding
