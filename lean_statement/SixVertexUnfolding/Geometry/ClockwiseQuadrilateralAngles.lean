import SixVertexUnfolding.Geometry.CounterclockwiseAddition
import SixVertexUnfolding.Geometry.TriangleEdgeFrontier

/-! The four pocket angles sum to two pi by adding its two clockwise triangle sums. -/

namespace SixVertexUnfolding

open Real EuclideanGeometry

/-- The interior corner for a clockwise boundary entering from `a` and leaving toward `c`. -/
noncomputable def clockwiseCorner (a b c : Plane) : ℝ := counterclockwiseAngle (a - b) (c - b)

/-- A clockwise triangle uses the ordinary, nonreflex corner at each vertex. -/
theorem clockwise_triangle_corner (a b c : Plane) (clockwise : det (b - a) (c - a) < 0) :
    clockwiseCorner a b c = angle a b c := by
  have positive : 0 < det (a - b) (c - b) := by
    rw [triangle_area_reverse_base a b c]
    exact neg_pos.mpr clockwise
  unfold clockwiseCorner counterclockwiseAngle
  rw [if_neg (not_lt_of_ge positive.le)]
  simp only [EuclideanGeometry.angle, vsub_eq_sub]

/-- Each clockwise constituent triangle contributes exactly pi. -/
theorem clockwise_triangle_angle_sum (a b c : Plane) (clockwise : det (b - a) (c - a) < 0) :
    clockwiseCorner c a b + clockwiseCorner a b c + clockwiseCorner b c a = π := by
  have at_b : det (c - b) (a - b) < 0 := by rwa [triangle_area_cycle a b c]
  have at_c : det (a - c) (b - c) < 0 := by
    rw [triangle_area_cycle b c a, triangle_area_cycle a b c]
    exact clockwise
  rw [clockwise_triangle_corner c a b at_c, clockwise_triangle_corner a b c clockwise,
    clockwise_triangle_corner b c a at_b]
  have different : b ≠ a := by intro same; rw [same, sub_self] at clockwise; simp [det] at clockwise
  have total := angle_add_angle_add_angle_eq_pi c different
  linarith

/-- Two adjacent positive triangle corners add to the full polygon corner, even when it is reflex. -/
theorem clockwiseCorner_add (a b c d : Plane)
    (first : 0 < det (a - b) (c - b)) (second : 0 < det (c - b) (d - b)) :
    clockwiseCorner a b d = clockwiseCorner a b c + clockwiseCorner c b d :=
  counterclockwiseAngle_add _ _ _ first second

/-- Either separating diagonal gives the same exact four-corner angle sum. -/
theorem clockwise_quadrilateral_angle_sum (a p b w : Plane)
    (orientation : (0 < det (b - a) (p - a) ∧ det (b - a) (w - a) < 0) ∨
      (det (w - p) (a - p) < 0 ∧ 0 < det (w - p) (b - p))) :
    clockwiseCorner w a p + clockwiseCorner a p b + clockwiseCorner p b w + clockwiseCorner b w a = 2 * π := by
  rcases orientation with first | second
  · have triangle : det (p - a) (b - a) < 0 := by rw [det_swap]; exact neg_neg_of_pos first.1
    have at_a : 0 < det (w - a) (b - a) := by rw [det_swap]; exact neg_pos.mpr first.2
    have at_b_left : 0 < det (p - b) (a - b) := by
      have identity : det (p - b) (a - b) = det (b - a) (p - a) := by simp only [det, PiLp.sub_apply]; ring
      rw [identity]
      exact first.1
    have at_b_right : 0 < det (a - b) (w - b) := by
      rw [triangle_area_reverse_base a b w]
      exact neg_pos.mpr first.2
    rw [clockwiseCorner_add w a b p at_a first.1, clockwiseCorner_add p b a w at_b_left at_b_right]
    linarith [clockwise_triangle_angle_sum a p b triangle, clockwise_triangle_angle_sum a b w first.2]
  · have triangle_left : det (p - a) (w - a) < 0 := by
      have identity : det (p - a) (w - a) = det (w - p) (a - p) := by simp only [det, PiLp.sub_apply]; ring
      rw [identity]
      exact second.1
    have triangle_right : det (b - p) (w - p) < 0 := by rw [det_swap]; exact neg_neg_of_pos second.2
    have at_p : 0 < det (a - p) (w - p) := by rw [det_swap]; exact neg_pos.mpr second.1
    have at_w_left : 0 < det (b - w) (p - w) := by
      have identity : det (b - w) (p - w) = det (w - p) (b - p) := by simp only [det, PiLp.sub_apply]; ring
      rw [identity]
      exact second.2
    have at_w_right : 0 < det (p - w) (a - w) := by
      have identity : det (p - w) (a - w) = -det (w - p) (a - p) := by simp only [det, PiLp.sub_apply]; ring
      rw [identity]
      exact neg_pos.mpr second.1
    rw [clockwiseCorner_add a p w b at_p second.2, clockwiseCorner_add b w p a at_w_left at_w_right]
    linarith [clockwise_triangle_angle_sum a p w triangle_left, clockwise_triangle_angle_sum p b w triangle_right]

/-- The overlap-contact corner contributes strictly positively in either diagonal branch. -/
theorem clockwise_quadrilateral_contact_pos (a p b w : Plane)
    (orientation : (0 < det (b - a) (p - a) ∧ det (b - a) (w - a) < 0) ∨
      (det (w - p) (a - p) < 0 ∧ 0 < det (w - p) (b - p))) :
    0 < clockwiseCorner a p b := by
  rcases orientation with first | second
  · have positive : 0 < det (a - p) (b - p) := by
      have identity : det (a - p) (b - p) = det (b - a) (p - a) := by simp only [det, PiLp.sub_apply]; ring
      rw [identity]
      exact first.1
    exact counterclockwiseAngle_pos_of_det_ne_zero _ _ positive.ne'
  · have positive : 0 < det (a - p) (w - p) := by rw [det_swap]; exact neg_pos.mpr second.1
    rw [clockwiseCorner_add a p w b positive second.2]
    exact add_pos (counterclockwiseAngle_pos_of_det_ne_zero _ _ positive.ne')
      (counterclockwiseAngle_pos_of_det_ne_zero _ _ second.2.ne')

end SixVertexUnfolding
