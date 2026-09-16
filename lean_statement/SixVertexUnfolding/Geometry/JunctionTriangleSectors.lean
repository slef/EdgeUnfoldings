import SixVertexUnfolding.Geometry.JoinedTriangles
import SixVertexUnfolding.Geometry.HingeDeterminant

/-! Adjacent angular gaps place their triangles on opposite sides of
the shared source ray. Their exact intersection is that radial segment.
-/

namespace SixVertexUnfolding

open Real Set

/-- Two consecutive gaps have triangles meeting exactly along their common
source ray, for arbitrary positive incident-edge lengths. -/
theorem consecutive_gap_triangles_intersection (z : Plane) {R L N α β γ : ℝ}
    (source_positive : 0 < R) (left_positive : 0 < L) (right_positive : 0 < N)
    (first_gap : α < β) (second_gap : β < γ)
    (first_width : β < α + 2 * π) (second_width : γ < β + 2 * π) :
    convexHull ℝ ({z + R • direction β, z, z + L • direction ((α + β) / 2)} : Set Plane) ∩
      convexHull ℝ ({z + R • direction β, z, z + N • direction ((β + γ) / 2)} : Set Plane) =
        segment ℝ (z + R • direction β) z := by
  have left_sine : sin (((α + β) / 2) - β) < 0 := by
    rw [show (α + β) / 2 - β = -((β - α) / 2) by ring, sin_neg]
    exact neg_neg_of_pos (sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
  have right_sine : 0 < sin (((β + γ) / 2) - β) :=
    sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have left_det : det ((z + R • direction β) - z)
      ((z + L • direction ((α + β) / 2)) - z) < 0 := by
    rw [add_sub_cancel_left, add_sub_cancel_left, det_smul_left, det_smul_right, direction_det]
    exact mul_neg_of_pos_of_neg source_positive (mul_neg_of_pos_of_neg left_positive left_sine)
  have right_det : 0 < det ((z + R • direction β) - z)
      ((z + N • direction ((β + γ) / 2)) - z) := by
    rw [add_sub_cancel_left, add_sub_cancel_left, det_smul_left, det_smul_right, direction_det]
    exact mul_pos source_positive (mul_pos right_positive right_sine)
  have intersection := opposite_triangles_intersection z (z + R • direction β)
    (z + L • direction ((α + β) / 2)) (z + N • direction ((β + γ) / 2))
    (mul_neg_of_neg_of_pos left_det right_det)
  simpa only [insert_comm (z + R • direction β) z, segment_symm ℝ (z + R • direction β) z]
    using intersection

end SixVertexUnfolding
