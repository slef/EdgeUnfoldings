import SixVertexUnfolding.Geometry.RadialSectorMembership

/-! A convex sector of width below pi has ordinary polar coordinates inside
its defining angular interval. -/

namespace SixVertexUnfolding

open Set Real

/-- The polar representative of a nonzero point in a short cone lies between its two rays. -/
theorem polar_representation_in_short_cone (α β : ℝ) (positive : 0 < β - α)
    (short : β - α < π) (x : Plane) (nonzero : x ≠ 0)
    (member : x ∈ twoRayCone (direction α) (direction β)) :
    ∃ θ, α ≤ θ ∧ θ ≤ β ∧ x = dist 0 x • direction θ := by
  obtain ⟨θ, lower, upper, expression⟩ := polar_representation_in_turn α x nonzero
  by_cases endpoint : θ = α + 2 * π
  · refine ⟨α, le_rfl, by linarith, ?_⟩
    simpa only [endpoint, direction_add_two_pi] using expression
  · refine ⟨θ, lower, ?_, expression⟩
    have area : 0 < det (direction α) (direction β) := by
      rw [direction_det]
      exact sin_pos_of_pos_of_lt_pi positive short
    have sides := (mem_twoRayCone_iff_dets _ _ _ area).mp member
    rw [expression, det_smul_right, direction_det] at sides
    have other : 0 ≤ dist 0 x * sin (β - θ) := by
      simpa only [det_smul_left, direction_det] using sides.2
    have radius : 0 < dist 0 x := dist_pos.mpr nonzero.symm
    apply angle_between_of_sector_heights α β θ (by linarith) (lt_of_le_of_ne upper endpoint)
    · exact (mul_nonneg_iff_of_pos_left radius).mp sides.1
    · exact (mul_nonneg_iff_of_pos_left radius).mp other

/-- Positive directions separated by less than pi have a strictly shorter chord than the route via zero. -/
theorem polar_chord_shorter_than_radii (r s α β : ℝ) (r_pos : 0 < r) (s_pos : 0 < s)
    (lower : 0 ≤ β - α) (upper : β - α < π) :
    dist (r • direction α) (s • direction β) < r + s := by
  have formula := polar_distance_sq r s α β
  have cosine : -1 < cos (β - α) := by
    have compared := strictAntiOn_cos ⟨lower, upper.le⟩ ⟨pi_pos.le, le_rfl⟩ upper
    simpa only [cos_pi] using compared
  have positive_product := mul_pos r_pos s_pos
  nlinarith [show 0 ≤ dist (r • direction α) (s • direction β) from dist_nonneg]

end SixVertexUnfolding
