import SixVertexUnfolding.Geometry.PolarArcs
import SixVertexUnfolding.Geometry.RegionSide

/-! Near the pole, the four-sided boundary leaves two open circular arcs free of boundary points. -/

namespace SixVertexUnfolding

open Real

/-- The distant sides miss a small ball; the two radial sides meet its circle only at their named angles. -/
theorem small_circle_arcs_avoid_frontier (region : Set Plane) (a p b : Plane)
    (rA rB α β : ℝ) (rA_pos : 0 < rA) (rB_pos : 0 < rB)
    (left : a = rA • direction α) (right : b = rB • direction β)
    (ordered : α < β) (one_turn : β < α + 2 * π)
    (boundary : frontier region = segment ℝ a p ∪ segment ℝ p b ∪ segment ℝ (0 : Plane) b ∪ segment ℝ (0 : Plane) a)
    (far_left : (0 : Plane) ∉ segment ℝ a p) (far_right : (0 : Plane) ∉ segment ℝ p b) :
    ∃ ε > 0, ∀ r : ℝ, 0 < r → r < ε →
      Disjoint ((fun θ => r • direction θ) '' Set.Ioo α β) (frontier region) ∧
      Disjoint ((fun θ => r • direction θ) '' Set.Ioo β (α + 2 * π)) (frontier region) := by
  have segment_closed (x y : Plane) : IsClosed (segment ℝ x y) := by
    rw [← convexHull_pair]
    exact (Set.toFinite ({x, y} : Set Plane)).isClosed_convexHull ℝ
  have closed : IsClosed (segment ℝ a p ∪ segment ℝ p b) :=
    (segment_closed a p).union (segment_closed p b)
  obtain ⟨ε, positive, neighborhood⟩ := Metric.isOpen_iff.mp closed.isOpen_compl 0
    (show (0 : Plane) ∉ segment ℝ a p ∪ segment ℝ p b from fun member => member.elim far_left far_right)
  refine ⟨ε, positive, fun r r_pos r_small => ?_⟩
  have safe (θ : ℝ) (after : α < θ) (before : θ < α + 2 * π) (different : θ ≠ β) :
      r • direction θ ∉ frontier region := by
    have distant : r • direction θ ∉ segment ℝ a p ∪ segment ℝ p b := by
      apply neighborhood
      rw [Metric.mem_ball, dist_comm, polar_radius r θ r_pos.le]
      exact r_small
    rw [boundary]
    rintro (((on_left | on_right) | on_last_ray) | on_first_ray)
    · exact distant (Or.inl on_left)
    · exact distant (Or.inr on_right)
    · rw [right] at on_last_ray
      exact polar_point_not_mem_radial_segment r rB θ β r_pos rB_pos.le
        (by linarith) (by linarith) different on_last_ray
    · rw [left] at on_first_ray
      exact polar_point_not_mem_radial_segment r rA θ α r_pos rA_pos.le
        (by linarith) (by linarith [pi_pos]) (ne_of_gt after) on_first_ray
  constructor
  · apply Set.disjoint_left.mpr
    rintro x ⟨θ, angle, rfl⟩ on_boundary
    exact safe θ angle.1 (by linarith [angle.2]) (ne_of_lt angle.2) on_boundary
  · apply Set.disjoint_left.mpr
    rintro x ⟨θ, angle, rfl⟩ on_boundary
    exact safe θ (by linarith [angle.1]) angle.2 (ne_of_gt angle.1) on_boundary

end SixVertexUnfolding
