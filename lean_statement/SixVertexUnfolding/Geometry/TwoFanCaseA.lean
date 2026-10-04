import SixVertexUnfolding.Geometry.TwoFanFrame
import SixVertexUnfolding.Geometry.PolygonCornerDirections
import SixVertexUnfolding.Geometry.WiderCutRays

/-! Case A for whole polygons attached to the two cap fans. Their supporting
cones, copied edge lengths, and full corner angles are the geometric inputs. -/

namespace SixVertexUnfolding

open Real EuclideanGeometry

/-- The wider Case A separator applies to whole outer polygons in their actual corner cones. -/
theorem two_fan_caseA (left : ThreeTriangleChain) (right : FourTriangleChain)
    (right_center : right.center = left.ray 1)
    (common_apex : right.ray 0 = left.ray 0) (left_center : right.ray 1 = left.center)
    (left_turn : (∑ i, left.corner i) < 2 * π) (right_turn : (∑ i, right.corner i) < 2 * π)
    (left_length : left.radius 3 = left.radius 0) (right_length : right.radius 4 = right.radius 0)
    (K L : Set Plane) (z w : Plane)
    (left_cone : K ⊆ translatedCone (left.ray 3) (left.center - left.ray 3) (z - left.ray 3))
    (right_cone : L ⊆ translatedCone (right.ray 4) (right.center - right.ray 4) (w - right.ray 4))
    (left_witness : left.ray 2 ∈ K) (right_witness : right.ray 3 ∈ L)
    (α β lam rho : ℝ)
    (left_direction : α + left.corner 1 + left.corner 2 = 2 * π)
    (right_direction : β + right.corner 1 + right.corner 2 + right.corner 3 = 2 * π)
    (left_angle : angle left.center (left.ray 3) z = lam)
    (right_angle : angle right.center (right.ray 4) w = rho)
    (lam_pos : 0 < lam) (lam_small : lam < π) (rho_pos : 0 < rho) (rho_small : rho < π)
    (narrow : α + β < π) (angle_sum : lam + rho < π + (α + β))
    (left_bound : lam ≤ (π + (α + β)) / 2) (right_bound : rho ≤ (π + (α + β)) / 2) :
    Disjoint (interior K) (interior L) := by
  obtain ⟨motion, at_left, at_right, left_rays, right_rays⟩ :=
    exists_two_fan_cap_frame left right right_center common_apex left_center
  have left_wider : left.corner 0 < α := by rw [Fin.sum_univ_three] at left_turn; linarith
  have right_wider : right.corner 0 < β := by rw [Fin.sum_univ_four] at right_turn; linarith
  have middle_left : motion (left.ray 0) = left.radius 0 • direction (left.corner 0) := by
    have h := left_rays 0
    simpa only [at_left, sub_zero, ThreeTriangleChain.capDirections, Matrix.cons_val_zero] using h
  have middle_right : motion (left.ray 0) = left.radius 1 • direction 0 +
      right.radius 0 • direction (π - right.corner 0) := by
    have h := right_rays 0
    change motion (right.ray 0) - motion right.center =
      right.radius 0 • direction (π - right.corner 0) at h
    rw [common_apex, at_right] at h
    exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)
  have left_last : direction (left.capDirections 3) = direction α := by
    change direction (-left.corner 1 - left.corner 2) = direction α
    rw [show α = (-left.corner 1 - left.corner 2) + 2 * π by linarith, direction_add_two_pi]
  have right_last : direction (right.capDirections 4) = direction (π - β) := by
    change direction (π + right.corner 1 + right.corner 2 + right.corner 3) = direction (π - β)
    rw [show π + right.corner 1 + right.corner 2 + right.corner 3 = (π - β) + 2 * π by linarith,
      direction_add_two_pi]
  have at_left_copy : motion (left.ray 3) = left.radius 0 • direction α := by
    have h := left_rays 3
    rwa [at_left, sub_zero, left_last, left_length] at h
  have at_right_copy : motion (right.ray 4) = left.radius 1 • direction 0 +
      right.radius 0 • direction (π - β) := by
    have h := right_rays 4
    rw [at_right, right_last, right_length] at h
    exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)
  have cones := CutRays.caseA_wider_cones (left.radius 1) (left.radius 0) (right.radius 0)
    α β (left.corner 0) (right.corner 0) lam rho (motion (left.ray 0))
    (left.radius_pos 1) (left.radius_pos 0) (right.radius_pos 0)
    (left.corner_pos 0) (right.corner_pos 0) left_wider right_wider narrow middle_left middle_right
    lam_pos lam_small rho_pos rho_small angle_sum left_bound right_bound
  have left_edge : motion left.center - motion (left.ray 3) = left.radius 0 • direction (π + α) := by
    rw [at_left, at_left_copy, show π + α = α + π by ring, direction_add_pi, smul_neg, zero_sub]
  have right_edge : motion right.center - motion (right.ray 4) = right.radius 0 • direction (-β) := by
    rw [at_right, at_right_copy, show π - β = -β + π by ring, direction_add_pi, smul_neg]
    module
  have left_measured : angle (motion left.center) (motion (left.ray 3)) (motion z) = lam := by
    have h := motion.toAffineIsometry.angle_map left.center (left.ray 3) z
    change angle (motion left.center) (motion (left.ray 3)) (motion z) = _ at h
    exact h.trans left_angle
  have right_measured : angle (motion right.center) (motion (right.ray 4)) (motion w) = rho := by
    have h := motion.toAffineIsometry.angle_map right.center (right.ray 4) w
    change angle (motion right.center) (motion (right.ray 4)) (motion w) = _ at h
    exact h.trans right_angle
  have left_side : det (motion left.center - motion (left.ray 3))
      (motion (left.ray 2) - motion (left.ray 3)) < 0 := by
    rw [corner_determinant_cyclic, left_rays 2, left_rays 3, det_smul_left, det_smul_right, direction_det]
    change left.radius 2 * (left.radius 3 * sin ((-left.corner 1 - left.corner 2) - -left.corner 1)) < 0
    rw [show (-left.corner 1 - left.corner 2) - -left.corner 1 = -left.corner 2 by ring, sin_neg]
    exact mul_neg_of_pos_of_neg (left.radius_pos 2) (mul_neg_of_pos_of_neg (left.radius_pos 3)
      (neg_neg_of_pos (sin_pos_of_pos_of_lt_pi (left.corner_pos 2) (left.corner_lt_pi 2))))
  have right_side : 0 < det (motion right.center - motion (right.ray 4))
      (motion (right.ray 3) - motion (right.ray 4)) := by
    rw [corner_determinant_cyclic, right_rays 3, right_rays 4, det_smul_left, det_smul_right, direction_det]
    change 0 < right.radius 3 * (right.radius 4 * sin
      ((π + right.corner 1 + right.corner 2 + right.corner 3) - (π + right.corner 1 + right.corner 2)))
    rw [show (π + right.corner 1 + right.corner 2 + right.corner 3) -
      (π + right.corner 1 + right.corner 2) = right.corner 3 by ring]
    exact mul_pos (right.radius_pos 3) (mul_pos (right.radius_pos 4)
      (sin_pos_of_pos_of_lt_pi (right.corner_pos 3) (right.corner_lt_pi 3)))
  have left_image := (Set.image_mono left_cone).trans
    (affine_image_corner_cone motion.toAffineMap (left.ray 3) left.center z)
  have right_image := (Set.image_mono right_cone).trans
    (affine_image_corner_cone motion.toAffineMap (right.ray 4) right.center w)
  have left_polar := clockwise_corner_cone (motion (left.ray 3)) (motion left.center) (motion z)
    (motion (left.ray 2)) (left.radius 0) (π + α) (left.radius_pos 0)
    (by rw [left_measured]; exact lam_pos) (by rw [left_measured]; exact lam_small) left_edge
    (left_image ⟨left.ray 2, left_witness, rfl⟩) left_side
  have right_polar := counterclockwise_corner_cone (motion (right.ray 4)) (motion right.center) (motion w)
    (motion (right.ray 3)) (right.radius 0) (-β) (right.radius_pos 0)
    (by rw [right_measured]; exact rho_pos) (by rw [right_measured]; exact rho_small) right_edge
    (right_image ⟨right.ray 3, right_witness, rfl⟩) right_side
  have left_contained := left_image.trans left_polar
  have right_contained := right_image.trans right_polar
  rw [left_measured, at_left_copy] at left_contained
  rw [right_measured, at_right_copy] at right_contained
  have safe := cones.mono (interior_mono left_contained) (interior_mono right_contained)
  change Disjoint (interior (motion.toHomeomorph '' K)) (interior (motion.toHomeomorph '' L)) at safe
  rw [← motion.toHomeomorph.image_interior, ← motion.toHomeomorph.image_interior] at safe
  exact (Set.disjoint_image_iff motion.injective).mp safe

end SixVertexUnfolding
