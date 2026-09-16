import SixVertexUnfolding.Geometry.RadialHinges
import SixVertexUnfolding.Geometry.DirectionIdentities

/-! The virtual intersection of two inward cut rays, with all lengths and signs explicit. -/

namespace SixVertexUnfolding.CutRays

open Real

noncomputable def leftLength (base α β : ℝ) : ℝ := base * sin β / sin (α + β)
noncomputable def rightLength (base α β : ℝ) : ℝ := base * sin α / sin (α + β)
noncomputable def intersection (base α β : ℝ) : Plane := leftLength base α β • direction α

variable {base α β : ℝ}

theorem sine_sum_pos (α_pos : 0 < α) (β_pos : 0 < β) (narrow : α + β < π) : 0 < sin (α + β) :=
  sin_pos_of_pos_of_lt_pi (by linarith) narrow

theorem leftLength_pos (base_pos : 0 < base) (α_pos : 0 < α) (β_pos : 0 < β) (narrow : α + β < π) :
    0 < leftLength base α β :=
  div_pos (mul_pos base_pos (sin_pos_of_pos_of_lt_pi β_pos (by linarith))) (sine_sum_pos α_pos β_pos narrow)

theorem rightLength_pos (base_pos : 0 < base) (α_pos : 0 < α) (β_pos : 0 < β) (narrow : α + β < π) :
    0 < rightLength base α β :=
  div_pos (mul_pos base_pos (sin_pos_of_pos_of_lt_pi α_pos (by linarith))) (sine_sum_pos α_pos β_pos narrow)

/-- The sine-rule lengths reach exactly the same point from both base endpoints. -/
theorem intersection_eq_from_right (α_pos : 0 < α) (β_pos : 0 < β) (narrow : α + β < π) :
    intersection base α β = base • direction 0 + rightLength base α β • direction (π - β) := by
  have nonzero := (sine_sum_pos α_pos β_pos narrow).ne'
  ext i
  fin_cases i
  · change (base * sin β / sin (α + β)) * cos α = base * cos 0 + (base * sin α / sin (α + β)) * cos (π - β)
    simp only [cos_zero, cos_pi_sub, mul_one]
    field_simp [nonzero]
    rw [sin_add]
    ring
  · change (base * sin β / sin (α + β)) * sin α = base * sin 0 + (base * sin α / sin (α + β)) * sin (π - β)
    simp only [sin_zero, sin_pi_sub, mul_zero, zero_add]
    ring

theorem intersection_noncollinear (base_pos : 0 < base) (α_pos : 0 < α) (β_pos : 0 < β) (narrow : α + β < π) :
    ¬ Collinear ℝ ({0, base • direction 0, intersection base α β} : Set Plane) := by
  apply radial_triangle_noncollinear _ _ _ _ base_pos (leftLength_pos base_pos α_pos β_pos narrow)
  · linarith
  · linarith

theorem intersection_left_distance (base_pos : 0 < base) (α_pos : 0 < α) (β_pos : 0 < β) (narrow : α + β < π) :
    dist 0 (intersection base α β) = leftLength base α β :=
  polar_radius _ _ (leftLength_pos base_pos α_pos β_pos narrow).le

theorem intersection_right_distance (base_pos : 0 < base) (α_pos : 0 < α) (β_pos : 0 < β) (narrow : α + β < π) :
    dist (base • direction 0) (intersection base α β) = rightLength base α β := by
  rw [intersection_eq_from_right α_pos β_pos narrow]
  simp only [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul, direction_norm, mul_one, Real.norm_eq_abs,
    abs_of_nonneg (rightLength_pos base_pos α_pos β_pos narrow).le]

end SixVertexUnfolding.CutRays
