import SixVertexUnfolding.Geometry.PolarArcs
import SixVertexUnfolding.Geometry.TriangleWeights
import SixVertexUnfolding.Geometry.TwoRayCones

/-! Signed side inequalities recover the actual angular interval of a finite radial triangle. -/

namespace SixVertexUnfolding

open Real

/-- Within one turn, the two inward heights force a ray into the sector of width below pi. -/
theorem angle_between_of_sector_heights (α β θ : ℝ) (width_pos : α < β)
    (end_turn : θ < α + 2 * π)
    (left : 0 ≤ sin (θ - α)) (right : 0 ≤ sin (β - θ)) : θ ≤ β := by
  by_contra after
  have after : β < θ := lt_of_not_ge after
  by_cases half_turn : θ - α ≤ π
  · have negative := sin_neg_of_neg_of_neg_pi_lt (show β - θ < 0 by linarith)
      (show -π < β - θ by linarith)
    linarith
  · have negative := sin_neg_of_neg_of_neg_pi_lt (show θ - α - 2 * π < 0 by linarith)
      (show -π < θ - α - 2 * π by linarith)
    rw [sin_sub_two_pi] at negative
    linarith

/-- A nonzero point of a radial triangle has its angle between the two endpoint directions. -/
theorem radial_triangle_polar_sector (r s t α β θ : ℝ) (r_pos : 0 < r) (s_pos : 0 < s) (t_pos : 0 < t)
    (width_pos : α < β) (width : β - α < π) (end_turn : θ < α + 2 * π)
    (member : t • direction θ ∈ convexHull ℝ ({0, r • direction α, s • direction β} : Set Plane)) : θ ≤ β := by
  have area : 0 < det (r • direction α) (s • direction β) := by
    rw [det_smul_left, det_smul_right, direction_det]
    exact mul_pos r_pos (mul_pos s_pos (sin_pos_of_pos_of_lt_pi (sub_pos.mpr width_pos) width))
  have cone : t • direction θ ∈ twoRayCone (r • direction α) (s • direction β) := by
    obtain ⟨u, v, z, hu, hv, hz, total, expression⟩ := triangle_weights _ _ _ _ member
    refine ⟨v, z, hv, hz, ?_⟩
    simpa only [smul_zero, zero_add] using expression.symm
  have sides := (mem_twoRayCone_iff_dets _ _ _ area).mp cone
  simp only [det_smul_left, det_smul_right, direction_det] at sides
  apply angle_between_of_sector_heights α β θ width_pos end_turn
  · have coefficient := mul_pos r_pos t_pos
    nlinarith [sides.1]
  · have coefficient := mul_pos t_pos s_pos
    nlinarith [sides.2]

end SixVertexUnfolding
