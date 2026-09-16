import SixVertexUnfolding.Geometry.RadialBaseDirections

/-! Exact copied-apex directions for a petal attached outward to a radial fan triangle. -/

namespace SixVertexUnfolding

open Real EuclideanGeometry

/-- At the first equator endpoint, outward flattening subtracts the full patch corner from the inward radial direction. -/
theorem outward_petal_direction_left (r s α β : ℝ) (r_pos : 0 < r) (s_pos : 0 < s)
    (width_pos : 0 < β - α) (width_small : β - α < π) (p : Plane)
    (noncollinear : ¬ Collinear ℝ ({r • direction α, s • direction β, p} : Set Plane))
    (outward : OppositeHingeSides (r • direction α) (s • direction β) 0 p) :
    p - r • direction α = dist p (r • direction α) •
      direction (α + π - (angle 0 (r • direction α) (s • direction β) +
        angle (s • direction β) (r • direction α) p)) := by
  let a := r • direction α
  let b := s • direction β
  let γ := angle 0 a b
  let ψ := angle b a p
  have fan_noncollinear := radial_triangle_noncollinear r s α β r_pos s_pos width_pos width_small
  have γ_pos : 0 < γ := angle_pos_of_not_collinear fan_noncollinear
  have γ_small : γ < π := angle_lt_pi_of_not_collinear fan_noncollinear
  have petal_noncollinear : ¬ Collinear ℝ ({b, a, p} : Set Plane) := by
    rw [Set.insert_comm]
    exact noncollinear
  have ψ_pos : 0 < ψ := angle_pos_of_not_collinear petal_noncollinear
  have ψ_small : ψ < π := angle_lt_pi_of_not_collinear petal_noncollinear
  have base_pos : 0 < dist a b := radial_base_dist_pos r s α β r_pos s_pos width_pos width_small
  have arm_pos : 0 < dist p a := by
    apply dist_pos.mpr
    intro same
    apply noncollinear
    change Collinear ℝ ({a, b, p} : Set Plane)
    have pair : ({a, b, p} : Set Plane) = {a, b} := by
      rw [same]
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [pair]
    exact collinear_pair ℝ a b
  have base : b - a = dist a b • direction (α + π - γ) :=
    radial_base_direction_left r s α β r_pos s_pos width_pos width_small
  have axis : r • direction (α + π) = -a := by rw [direction_add_pi, smul_neg]
  have measured : angle (dist a b • direction (α + π - γ)) 0 (p - a) = ψ := by
    rw [← base]
    change InnerProductGeometry.angle ((b - a) - 0) ((p - a) - 0) = InnerProductGeometry.angle (b - a) (p - a)
    simp only [sub_zero]
  have side : OppositeHingeSides 0 (dist a b • direction (α + π - γ)) (r • direction (α + π)) (p - a) := by
    rw [← base, axis]
    simpa only [OppositeHingeSides, hingeSideVector, sub_zero, zero_sub] using outward
  have placed := outward_radial_point_down r (dist a b) (dist p a) (α + π) (α + π - γ) ψ
    r_pos base_pos arm_pos (by linarith) (by linarith) ψ_pos ψ_small (p - a)
    (by simp only [dist_eq_norm, zero_sub, norm_neg]) measured side
  have direction_eq : α + π - γ - ψ = α + π - (γ + ψ) := by ring
  simpa only [direction_eq] using placed

/-- At the last endpoint, the full patch corner is added to the inward radial direction. -/
theorem outward_petal_direction_right (r s α β : ℝ) (r_pos : 0 < r) (s_pos : 0 < s)
    (width_pos : 0 < β - α) (width_small : β - α < π) (p : Plane)
    (noncollinear : ¬ Collinear ℝ ({r • direction α, s • direction β, p} : Set Plane))
    (outward : OppositeHingeSides (r • direction α) (s • direction β) 0 p) :
    p - s • direction β = dist p (s • direction β) •
      direction (β - π + (angle 0 (s • direction β) (r • direction α) +
        angle (r • direction α) (s • direction β) p)) := by
  let a := r • direction α
  let b := s • direction β
  let γ := angle 0 b a
  let ψ := angle a b p
  have reorder : ({0, b, a} : Set Plane) = {0, a, b} := by
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have fan_noncollinear : ¬ Collinear ℝ ({0, b, a} : Set Plane) := by
    rw [reorder]
    exact radial_triangle_noncollinear r s α β r_pos s_pos width_pos width_small
  have γ_pos : 0 < γ := angle_pos_of_not_collinear fan_noncollinear
  have γ_small : γ < π := angle_lt_pi_of_not_collinear fan_noncollinear
  have ψ_pos : 0 < ψ := angle_pos_of_not_collinear noncollinear
  have ψ_small : ψ < π := angle_lt_pi_of_not_collinear noncollinear
  have base_pos : 0 < dist a b := radial_base_dist_pos r s α β r_pos s_pos width_pos width_small
  have arm_pos : 0 < dist p b := by
    apply dist_pos.mpr
    intro same
    apply noncollinear
    change Collinear ℝ ({a, b, p} : Set Plane)
    simpa [same] using collinear_pair ℝ a b
  have base : a - b = dist a b • direction (β - π + γ) :=
    radial_base_direction_right r s α β r_pos s_pos width_pos width_small
  have axis : s • direction (β - π) = -b := by rw [direction_sub_pi, smul_neg]
  have measured : angle (dist a b • direction (β - π + γ)) 0 (p - b) = ψ := by
    rw [← base]
    change InnerProductGeometry.angle ((a - b) - 0) ((p - b) - 0) = InnerProductGeometry.angle (a - b) (p - b)
    simp only [sub_zero]
  have reversed : OppositeHingeSides b a 0 p :=
    (oppositeHingeSides_swap a b 0 p (dist_pos.mp base_pos)).mpr outward
  have side : OppositeHingeSides 0 (dist a b • direction (β - π + γ)) (s • direction (β - π)) (p - b) := by
    rw [← base, axis]
    simpa only [OppositeHingeSides, hingeSideVector, sub_zero, zero_sub] using reversed
  have placed := outward_radial_point s (dist a b) (dist p b) (β - π) (β - π + γ) ψ
    s_pos base_pos arm_pos (by linarith) (by linarith) ψ_pos ψ_small (p - b)
    (by simp only [dist_eq_norm, zero_sub, norm_neg]) measured side
  have direction_eq : β - π + γ + ψ = β - π + (γ + ψ) := by ring
  simpa only [direction_eq] using placed

end SixVertexUnfolding
