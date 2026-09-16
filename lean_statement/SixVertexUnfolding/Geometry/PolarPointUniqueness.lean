import SixVertexUnfolding.Geometry.HingeDeterminant
import SixVertexUnfolding.Geometry.RadialHinges

/-! A radius, an ordinary corner angle, and the correct side determine a polar point. -/

namespace SixVertexUnfolding

open Real EuclideanGeometry

/-- The side condition resolves the two possible points with the same radius and angle cosine. -/
theorem polar_point_eq_of_cos_and_side (r s β γ : ℝ) (r_pos : 0 < r) (s_pos : 0 < s) (x : Plane)
    (radius : dist 0 x = s)
    (cosine : cos (angle (r • direction β) 0 x) = cos (γ - β))
    (side : 0 ≤ det (direction β) x * sin (γ - β)) : x = s • direction γ := by
  apply point_eq_of_hinge_distances 0 (r • direction β) x (s • direction γ)
    (dist_pos.mp (by rw [polar_radius r β r_pos.le]; exact r_pos))
  · rw [radius, polar_radius s γ s_pos.le]
  · apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
    rw [polar_distance_sq]
    have law := law_cos (r • direction β) 0 x
    simp only [← sq, dist_comm (r • direction β) 0, dist_comm x 0,
      polar_radius r β r_pos.le, radius, cosine] at law
    exact law
  · have normalized : NormedSpace.normalize (r • direction β) = direction β := by
      rw [NormedSpace.normalize_smul_of_pos r_pos,
        NormedSpace.normalize_eq_self_of_norm_eq_one (direction_norm β)]
    simp only [hingeSideVector, sub_zero, normalized]
    rw [hingeRemainder_inner_eq_det _ _ _ (direction_norm β), det_smul_right, direction_det]
    nlinarith [mul_nonneg s_pos.le side]

/-- One outward triangle adds its positive corner angle to the preceding polar direction. -/
theorem outward_radial_point (r s t α β φ : ℝ) (r_pos : 0 < r) (s_pos : 0 < s) (t_pos : 0 < t)
    (first_pos : 0 < β - α) (first_small : β - α < π) (φ_pos : 0 < φ) (φ_small : φ < π)
    (x : Plane) (radius : dist 0 x = t) (corner : angle (s • direction β) 0 x = φ)
    (outward : OppositeHingeSides 0 (s • direction β) (r • direction α) x) :
    x = t • direction (β + φ) := by
  apply polar_point_eq_of_cos_and_side s t β (β + φ) s_pos t_pos x radius
  · rw [corner]
    congr 1
    ring
  · rw [show β + φ - β = φ by ring]
    rw [oppositeHingeSides_iff_det 0 _ _ _ (dist_pos.mp (by rw [polar_radius s β s_pos.le]; exact s_pos))] at outward
    simp only [sub_zero, det_smul_left, det_smul_right, direction_det] at outward
    have negative : sin (α - β) < 0 := sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)
    have coefficient : s * (r * sin (α - β)) * s < 0 := by
      exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg s_pos (mul_neg_of_pos_of_neg r_pos negative)) s_pos
    have transverse : 0 ≤ det (direction β) x := by nlinarith
    exact mul_nonneg transverse (sin_pos_of_pos_of_lt_pi φ_pos φ_small).le

/-- The reflected orientation subtracts the new positive corner angle. -/
theorem outward_radial_point_down (r s t α β φ : ℝ) (r_pos : 0 < r) (s_pos : 0 < s) (t_pos : 0 < t)
    (first_pos : 0 < α - β) (first_small : α - β < π) (φ_pos : 0 < φ) (φ_small : φ < π)
    (x : Plane) (radius : dist 0 x = t) (corner : angle (s • direction β) 0 x = φ)
    (outward : OppositeHingeSides 0 (s • direction β) (r • direction α) x) :
    x = t • direction (β - φ) := by
  apply polar_point_eq_of_cos_and_side s t β (β - φ) s_pos t_pos x radius
  · rw [corner, show β - φ - β = -φ by ring, cos_neg]
  · rw [show β - φ - β = -φ by ring, sin_neg]
    rw [oppositeHingeSides_iff_det 0 _ _ _ (dist_pos.mp (by rw [polar_radius s β s_pos.le]; exact s_pos))] at outward
    simp only [sub_zero, det_smul_left, det_smul_right, direction_det] at outward
    have positive : 0 < sin (α - β) := sin_pos_of_pos_of_lt_pi first_pos first_small
    have coefficient : 0 < s * (r * sin (α - β)) * s :=
      mul_pos (mul_pos s_pos (mul_pos r_pos positive)) s_pos
    have transverse : det (direction β) x ≤ 0 := by nlinarith
    exact mul_nonneg_of_nonpos_of_nonpos transverse (neg_nonpos.mpr (sin_pos_of_pos_of_lt_pi φ_pos φ_small).le)

end SixVertexUnfolding
