import SixVertexUnfolding.Geometry.CutRayIntersection
import SixVertexUnfolding.Geometry.TriangleHalfplanes
import SixVertexUnfolding.Geometry.OppositeConeComparison

/-! The first opposite-petal case: a middle triangle strictly inside the virtual cut-ray triangle separates the apex cones. -/

namespace SixVertexUnfolding.CutRays

open Real

theorem polar_det_pos {r s α β : ℝ} (r_pos : 0 < r) (s_pos : 0 < s)
    (angle_pos : 0 < β - α) (angle_small : β - α < π) :
    0 < det (r • direction α) (s • direction β) := by
  rw [det_smul_left, det_smul_right, direction_det]
  exact mul_pos r_pos (mul_pos s_pos (sin_pos_of_pos_of_lt_pi angle_pos angle_small))

/-- Widening both positive base angles puts the original apex inside the virtual triangle, away from its apex. -/
theorem middle_apex_in_virtual_triangle (base s t α β φ ψ : ℝ) (m : Plane)
    (base_pos : 0 < base) (s_pos : 0 < s) (t_pos : 0 < t)
    (φ_pos : 0 < φ) (ψ_pos : 0 < ψ) (left_wider : φ < α) (right_wider : ψ < β)
    (narrow : α + β < π)
    (middle_left : m = s • direction φ)
    (middle_right : m = base • direction 0 + t • direction (π - ψ)) :
    m ∈ convexHull ℝ ({0, base • direction 0, intersection base α β} : Set Plane) ∧
      m ≠ intersection base α β := by
  have α_pos : 0 < α := φ_pos.trans left_wider
  have β_pos : 0 < β := ψ_pos.trans right_wider
  have L_pos := leftLength_pos base_pos α_pos β_pos narrow
  have R_pos := rightLength_pos base_pos α_pos β_pos narrow
  have area_pos : 0 < det (base • direction 0) (intersection base α β) :=
    polar_det_pos base_pos L_pos (by linarith) (by linarith)
  have base_side : 0 < det (base • direction 0) m := by
    rw [middle_left]
    exact polar_det_pos base_pos s_pos (by linarith) (by linarith)
  have left_side : 0 < det m (intersection base α β) := by
    rw [middle_left]
    exact polar_det_pos s_pos L_pos (by linarith) (by linarith)
  have right_side : 0 < det (intersection base α β - base • direction 0) (m - base • direction 0) := by
    have virtual_vector : intersection base α β - base • direction 0 = rightLength base α β • direction (π - β) := by
      rw [intersection_eq_from_right α_pos β_pos narrow]
      module
    have middle_vector : m - base • direction 0 = t • direction (π - ψ) := by rw [middle_right]; module
    rw [virtual_vector, middle_vector]
    exact polar_det_pos R_pos t_pos (by linarith) (by linarith)
  refine ⟨triangle_mem_of_three_halfplanes _ _ _ area_pos base_side.le left_side.le right_side.le, ?_⟩
  intro same
  rw [same, det_self] at left_side
  linarith

/-- The entire opposite apex cones are disjoint when the widened base angles total less than pi. -/
theorem caseA_opposed_apex_cones (base s t α β φ ψ : ℝ) (m : Plane)
    (base_pos : 0 < base) (s_pos : 0 < s) (t_pos : 0 < t)
    (φ_pos : 0 < φ) (ψ_pos : 0 < ψ) (left_wider : φ < α) (right_wider : ψ < β)
    (narrow : α + β < π)
    (middle_left : m = s • direction φ)
    (middle_right : m = base • direction 0 + t • direction (π - ψ)) :
    Disjoint (translatedCone (s • direction α) (-direction α) (direction (π - β)))
      (translatedCone (base • direction 0 + t • direction (π - β)) (direction α) (-direction (π - β))) := by
  have α_pos : 0 < α := φ_pos.trans left_wider
  have β_pos : 0 < β := ψ_pos.trans right_wider
  obtain ⟨contained, not_apex⟩ := middle_apex_in_virtual_triangle base s t α β φ ψ m
    base_pos s_pos t_pos φ_pos ψ_pos left_wider right_wider narrow middle_left middle_right
  have independent : det (-direction α) (direction (π - β)) ≠ 0 := by
    rw [det_neg_left, direction_det, show π - β - α = π - (α + β) by ring, sin_pi_sub]
    exact neg_ne_zero.mpr (sine_sum_pos α_pos β_pos narrow).ne'
  have left_radius : dist m 0 = s := by rw [middle_left, dist_comm]; exact polar_radius _ _ s_pos.le
  have right_radius : dist m (base • direction 0) = t := by
    rw [middle_right]
    simp only [dist_eq_norm, add_sub_cancel_left, norm_smul, direction_norm, mul_one, Real.norm_eq_abs, abs_of_nonneg t_pos.le]
  have virtual_left_radius : dist (intersection base α β) 0 = leftLength base α β := by
    rw [dist_comm]
    exact intersection_left_distance base_pos α_pos β_pos narrow
  have virtual_right_radius : dist (intersection base α β) (base • direction 0) = rightLength base α β := by
    rw [dist_comm]
    exact intersection_right_distance base_pos α_pos β_pos narrow
  have separated := opposite_cones_disjoint_from_virtual_triangle (0 : Plane) (base • direction 0)
    (intersection base α β) m (s • direction α) (base • direction 0 + t • direction (π - β))
    (-direction α) (direction (π - β)) independent (intersection_noncollinear base_pos α_pos β_pos narrow)
    contained not_apex
    (by rw [left_radius]; module)
    (by rw [right_radius])
    (by rw [virtual_left_radius]; unfold intersection; module)
    (by rw [virtual_right_radius]; exact intersection_eq_from_right α_pos β_pos narrow)
  simpa only [neg_neg] using separated

end SixVertexUnfolding.CutRays
