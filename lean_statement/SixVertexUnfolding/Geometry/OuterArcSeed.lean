import SixVertexUnfolding.Geometry.SmallCircleBoundary

/-! Excluding the through-fan arc forces an interior seed on the other arc near the pole. -/

namespace SixVertexUnfolding

open Real

/-- A regular region with two radial boundary sides occupies the other arc if one arc has an exterior ray.
The seed can be chosen arbitrarily close to the pole. -/
theorem exists_outer_arc_seed (region : Set Plane) (a p b : Plane)
    (closed : IsClosed region) (regular : closure (interior region) = region)
    (rA rB α β : ℝ) (rA_pos : 0 < rA) (rB_pos : 0 < rB)
    (left : a = rA • direction α) (right : b = rB • direction β)
    (ordered : α < β) (one_turn : β < α + 2 * π)
    (boundary : frontier region = segment ℝ a p ∪ segment ℝ p b ∪ segment ℝ (0 : Plane) b ∪ segment ℝ (0 : Plane) a)
    (far_left : (0 : Plane) ∉ segment ℝ a p) (far_right : (0 : Plane) ∉ segment ℝ p b)
    (γ η : ℝ) (inner_angle : α < γ ∧ γ < β) (outer_angle : β < η ∧ η < α + 2 * π)
    (ε_out : ℝ) (ε_out_pos : 0 < ε_out)
    (outside : ∀ r : ℝ, 0 < r → r < ε_out → r • direction γ ∉ interior region)
    (limit : ℝ) (limit_pos : 0 < limit) :
    ∃ r : ℝ, 0 < r ∧ r < limit ∧ r • direction η ∈ interior region := by
  obtain ⟨ε_boundary, ε_boundary_pos, arcs_safe⟩ := small_circle_arcs_avoid_frontier region a p b
    rA rB α β rA_pos rB_pos left right ordered one_turn boundary far_left far_right
  let ε := min limit (min ε_boundary (min ε_out (min rA rB)))
  have ε_pos : 0 < ε := lt_min limit_pos (lt_min ε_boundary_pos (lt_min ε_out_pos (lt_min rA_pos rB_pos)))
  have pole_boundary : (0 : Plane) ∈ frontier region := by
    rw [boundary]
    exact Or.inr (left_mem_segment ℝ 0 a)
  have pole_closure : (0 : Plane) ∈ closure (interior region) := by
    rw [regular]
    exact closed.frontier_subset pole_boundary
  obtain ⟨q, inside, close⟩ := Metric.mem_closure_iff.mp pole_closure ε ε_pos
  have not_boundary : q ∉ frontier region := fun member => member.2 inside
  have nonzero : q ≠ 0 := by
    intro same
    exact not_boundary (same ▸ pole_boundary)
  let r := dist (0 : Plane) q
  have r_pos : 0 < r := dist_pos.mpr nonzero.symm
  have r_limit : r < limit := close.trans_le (min_le_left _ _)
  have r_boundary : r < ε_boundary := close.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have r_out : r < ε_out := close.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have r_a : r < rA := close.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))))
  have r_b : r < rB := close.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))))
  have radial_member (R φ : ℝ) (positive : 0 < R) (short : r < R) :
      r • direction φ ∈ segment ℝ (0 : Plane) (R • direction φ) := by
    refine ⟨1 - r / R, r / R, sub_nonneg.mpr ((div_le_one₀ positive).mpr short.le),
      div_nonneg r_pos.le positive.le, by ring, ?_⟩
    simp only [smul_zero, zero_add, smul_smul, div_mul_cancel₀ r positive.ne']
  have off_first : q ∉ segment ℝ (0 : Plane) a := fun on_side => not_boundary (by rw [boundary]; exact Or.inr on_side)
  have off_last : q ∉ segment ℝ (0 : Plane) b := fun on_side => not_boundary (by rw [boundary]; exact Or.inl (Or.inr on_side))
  obtain ⟨θ, θ_lower, θ_upper, polar⟩ := polar_representation_in_turn α q nonzero
  have lower : α < θ := by
    apply lt_of_le_of_ne θ_lower
    intro same
    apply off_first
    rw [polar, ← same, left]
    exact radial_member rA α rA_pos r_a
  have upper : θ < α + 2 * π := by
    apply lt_of_le_of_ne θ_upper
    intro same
    apply off_first
    rw [polar, same, direction_add_two_pi, left]
    exact radial_member rA α rA_pos r_a
  have distinct : θ ≠ β := by
    intro same
    apply off_last
    rw [polar, same, right]
    exact radial_member rB β rB_pos r_b
  have safe := arcs_safe r r_pos r_boundary
  have after : β < θ := by
    by_contra before
    have θ_inner : θ < β := lt_of_le_of_ne (le_of_not_gt before) distinct
    have on_arc : q ∈ (fun φ => r • direction φ) '' Set.Ioo α β := ⟨θ, ⟨lower, θ_inner⟩, polar.symm⟩
    have arc_inside := preconnected_set_in_region region _ closed (polar_arc_preconnected r α β) safe.1 q on_arc inside
    exact outside r r_pos r_out (arc_inside ⟨γ, inner_angle, rfl⟩)
  have on_arc : q ∈ (fun φ => r • direction φ) '' Set.Ioo β (α + 2 * π) := ⟨θ, ⟨after, upper⟩, polar.symm⟩
  have arc_inside := preconnected_set_in_region region _ closed
    (polar_arc_preconnected r β (α + 2 * π)) safe.2 q on_arc inside
  exact ⟨r, r_pos, r_limit, arc_inside ⟨η, outer_angle, rfl⟩⟩

end SixVertexUnfolding
