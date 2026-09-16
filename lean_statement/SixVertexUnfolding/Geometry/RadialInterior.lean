import SixVertexUnfolding.Geometry.TriangleEdgeHalfplanes
import SixVertexUnfolding.Geometry.PlanarSectors

/-! A strict angular direction enters a radial triangle at every sufficiently small positive radius. -/

namespace SixVertexUnfolding

open Real

/-- The two radial side inequalities are strict; continuity handles the distant third side. -/
theorem small_ray_in_triangle_interior (a b v : Plane) (area : 0 < det a b)
    (left : 0 < det a v) (right : 0 < det v b) :
    ∃ ε > 0, ∀ r : ℝ, 0 < r → r < ε → r • v ∈ interior (convexHull ℝ ({0, a, b} : Set Plane)) := by
  have continuous_height : Continuous (fun r : ℝ => det (b - a) (r • v - a)) :=
    (detHeight (b - a)).continuous.comp ((continuous_id.smul continuous_const).sub continuous_const)
  have open_height : IsOpen {r : ℝ | 0 < det (b - a) (r • v - a)} :=
    isOpen_lt continuous_const continuous_height
  have at_zero : (0 : ℝ) ∈ {r : ℝ | 0 < det (b - a) (r • v - a)} := by
    change 0 < det (b - a) ((0 : ℝ) • v - a)
    have identity : det (b - a) (0 - a) = det a b := by
      simp only [det, PiLp.sub_apply, PiLp.zero_apply]
      ring
    simpa only [zero_smul, identity] using area
  obtain ⟨ε, positive, neighborhood⟩ := Metric.isOpen_iff.mp open_height 0 at_zero
  refine ⟨ε, positive, fun r r_pos r_small => ?_⟩
  apply triangle_interior_of_strict_edge_sides 0 a b (r • v)
  · simpa only [sub_zero] using area
  · simpa only [sub_zero, det_smul_right] using mul_pos r_pos left
  · apply neighborhood
    simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos r_pos] using r_small
  · have identity : det (0 - b) (r • v - b) = r * det v b := by
      simp only [det, PiLp.sub_apply, PiLp.zero_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    rw [identity]
    exact mul_pos r_pos right

/-- Every strict interior angle supplies an eventual interior seed in the finite radial triangle. -/
theorem small_polar_ray_in_radial_triangle (r s α β θ : ℝ) (r_pos : 0 < r) (s_pos : 0 < s)
    (left : α < θ) (right : θ < β) (width : β - α < π) :
    ∃ ε > 0, ∀ t : ℝ, 0 < t → t < ε → t • direction θ ∈ interior (radialTriangle r s α β) := by
  apply small_ray_in_triangle_interior
  · rw [det_smul_left, det_smul_right, direction_det]
    exact mul_pos r_pos (mul_pos s_pos (sin_pos_of_pos_of_lt_pi (by linarith) width))
  · rw [det_smul_left, direction_det]
    exact mul_pos r_pos (sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
  · rw [det_smul_right, direction_det]
    exact mul_pos s_pos (sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))

end SixVertexUnfolding
