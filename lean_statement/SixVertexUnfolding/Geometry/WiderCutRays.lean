import SixVertexUnfolding.Geometry.CaseASeparation
import SixVertexUnfolding.Geometry.WiderApexCones

/-! The wider Case A separator, with its strict distance sum supplied by the actual middle triangle. -/

namespace SixVertexUnfolding.CutRays

open Real

theorem middle_radius_sum_lt (base s t α β φ ψ : ℝ) (m : Plane)
    (base_pos : 0 < base) (s_pos : 0 < s) (t_pos : 0 < t)
    (φ_pos : 0 < φ) (ψ_pos : 0 < ψ) (left_wider : φ < α) (right_wider : ψ < β)
    (narrow : α + β < π) (middle_left : m = s • direction φ)
    (middle_right : m = base • direction 0 + t • direction (π - ψ)) :
    s + t < leftLength base α β + rightLength base α β := by
  have α_pos : 0 < α := φ_pos.trans left_wider
  have β_pos : 0 < β := ψ_pos.trans right_wider
  obtain ⟨contained, not_apex⟩ := middle_apex_in_virtual_triangle base s t α β φ ψ m
    base_pos s_pos t_pos φ_pos ψ_pos left_wider right_wider narrow middle_left middle_right
  have strict := triangle_distance_sum_lt_of_noncollinear (0 : Plane) (base • direction 0) (intersection base α β) m
    (intersection_noncollinear base_pos α_pos β_pos narrow) contained not_apex
  have left_radius : dist m 0 = s := by rw [middle_left, dist_comm]; exact polar_radius _ _ s_pos.le
  have right_radius : dist m (base • direction 0) = t := by
    rw [middle_right]
    simp only [dist_eq_norm, add_sub_cancel_left, norm_smul, direction_norm, mul_one, Real.norm_eq_abs, abs_of_pos t_pos]
  simpa only [left_radius, right_radius, dist_comm (intersection base α β),
    intersection_left_distance base_pos α_pos β_pos narrow,
    intersection_right_distance base_pos α_pos β_pos narrow] using strict

theorem cut_apex_displacement (base s t α β : ℝ)
    (α_pos : 0 < α) (β_pos : 0 < β) (narrow : α + β < π) :
    (base • direction 0 + t • direction (π - β)) - s • direction α =
      (s - leftLength base α β) • direction (π + α) +
        (t - rightLength base α β) • direction (π - β) := by
  have intersection_eq := intersection_eq_from_right (base := base) α_pos β_pos narrow
  have base_eq : base • direction 0 = leftLength base α β • direction α - rightLength base α β • direction (π - β) := by
    change leftLength base α β • direction α = _ at intersection_eq
    rw [intersection_eq]
    module
  rw [base_eq, show π + α = α + π by ring, direction_add_pi]
  module

/-- Both wider outer-angle bounds suffice; one of the two cut rays is necessarily short. -/
theorem caseA_wider_cones (base s t α β φ ψ lam rho : ℝ) (m : Plane)
    (base_pos : 0 < base) (s_pos : 0 < s) (t_pos : 0 < t)
    (φ_pos : 0 < φ) (ψ_pos : 0 < ψ) (left_wider : φ < α) (right_wider : ψ < β)
    (narrow : α + β < π) (middle_left : m = s • direction φ)
    (middle_right : m = base • direction 0 + t • direction (π - ψ))
    (lam_pos : 0 < lam) (lam_small : lam < π) (rho_pos : 0 < rho) (rho_small : rho < π)
    (angle_sum : lam + rho < π + (α + β))
    (left_bound : lam ≤ (π + (α + β)) / 2) (right_bound : rho ≤ (π + (α + β)) / 2) :
    Disjoint (interior (translatedCone (s • direction α) (direction (π + α - lam)) (direction (π + α))))
      (interior (translatedCone (base • direction 0 + t • direction (π - β)) (direction (-β)) (direction (-β + rho)))) := by
  have α_pos : 0 < α := φ_pos.trans left_wider
  have β_pos : 0 < β := ψ_pos.trans right_wider
  have strict := middle_radius_sum_lt base s t α β φ ψ m base_pos s_pos t_pos φ_pos ψ_pos
    left_wider right_wider narrow middle_left middle_right
  have displacement := cut_apex_displacement base s t α β α_pos β_pos narrow
  have separated := wider_apex_cones (s • direction α) (base • direction 0 + t • direction (π - β))
    (π - β) (α + β) lam rho (s - leftLength base α β) (t - rightLength base α β)
    (by linarith) narrow lam_pos lam_small rho_pos rho_small angle_sum left_bound right_bound (by linarith)
    (by rw [show π - β + (α + β) = π + α by ring]; exact displacement)
  have first_angle : π - β + (α + β) = π + α := by ring
  have right_first : -direction (π - β) = direction (-β) := by
    rw [show π - β = -β + π by ring, direction_add_pi, neg_neg]
  have right_last : -direction (π - β + rho) = direction (-β + rho) := by
    rw [show π - β + rho = (-β + rho) + π by ring, direction_add_pi, neg_neg]
  simpa only [first_angle, right_first, right_last] using separated

end SixVertexUnfolding.CutRays
