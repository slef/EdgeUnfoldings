import SixVertexUnfolding.Geometry.TwoRayCones
import SixVertexUnfolding.Geometry.PolarPointUniqueness

/-! A triangle fits in an apex cone whenever its apex angle fits between the two boundary rays. -/

namespace SixVertexUnfolding

open Real EuclideanGeometry

theorem twoRayCone_swap (e f : Plane) : twoRayCone e f = twoRayCone f e := by
  ext x
  constructor <;> rintro ⟨a, b, ha, hb, equal⟩ <;>
    exact ⟨b, a, hb, ha, equal.trans (add_comm _ _)⟩

theorem smul_mem_twoRayCone {e f x : Plane} {r : ℝ} (nonnegative : 0 ≤ r)
    (member : x ∈ twoRayCone e f) : r • x ∈ twoRayCone e f := by
  obtain ⟨a, b, ha, hb, rfl⟩ := member
  exact ⟨r * a, r * b, mul_nonneg nonnegative ha, mul_nonneg nonnegative hb, by module⟩

theorem translatedCone_convex (p e f : Plane) : Convex ℝ (translatedCone p e f) := by
  intro x hx y hy a b ha hb total
  have member := twoRayCone_convex e f hx hy ha hb total
  change a • x + b • y - p ∈ twoRayCone e f
  have coefficient : a = 1 - b := by linarith
  rw [coefficient] at member ⊢
  convert member using 1
  module

theorem triangle_in_cone_of_corner_vectors (p a b e f : Plane)
    (first : a - p ∈ twoRayCone e f) (second : b - p ∈ twoRayCone e f) :
    convexHull ℝ ({a, b, p} : Set Plane) ⊆ translatedCone p e f := by
  apply convexHull_min _ (translatedCone_convex p e f)
  intro x member
  rcases member with same | same | same
  · rw [same]; exact first
  · rw [same]; exact second
  · change x = p at same
    rw [same]
    change p - p ∈ twoRayCone e f
    rw [sub_self]
    exact zero_mem_twoRayCone e f

/-- The signed side chooses the clockwise realization of the measured apex angle. -/
theorem clockwise_corner_vector (p a z : Plane) (r β : ℝ) (r_pos : 0 < r)
    (length_pos : 0 < dist p z) (corner_pos : 0 < angle a p z) (corner_small : angle a p z < π)
    (first : a - p = r • direction β) (side : det (a - p) (z - p) ≤ 0) :
    z - p = dist p z • direction (β - angle a p z) := by
  have measured : angle (r • direction β) 0 (z - p) = angle a p z := by
    change InnerProductGeometry.angle (r • direction β - 0) (z - p - 0) =
      InnerProductGeometry.angle (a - p) (z - p)
    rw [sub_zero, sub_zero, first]
  apply polar_point_eq_of_cos_and_side r _ β _ r_pos length_pos
  · simp only [dist_eq_norm, zero_sub, norm_neg, norm_sub_rev]
  · rw [measured, show β - angle a p z - β = -angle a p z by ring, cos_neg]
  · rw [first, det_smul_left] at side
    have signed : det (direction β) (z - p) ≤ 0 := by nlinarith
    rw [show β - angle a p z - β = -angle a p z by ring, sin_neg]
    exact mul_nonneg_of_nonpos_of_nonpos signed (neg_nonpos.mpr (sin_pos_of_pos_of_lt_pi corner_pos corner_small).le)

theorem counterclockwise_corner_vector (p a z : Plane) (r β : ℝ) (r_pos : 0 < r)
    (length_pos : 0 < dist p z) (corner_pos : 0 < angle a p z) (corner_small : angle a p z < π)
    (first : a - p = r • direction β) (side : 0 ≤ det (a - p) (z - p)) :
    z - p = dist p z • direction (β + angle a p z) := by
  have measured : angle (r • direction β) 0 (z - p) = angle a p z := by
    change InnerProductGeometry.angle (r • direction β - 0) (z - p - 0) =
      InnerProductGeometry.angle (a - p) (z - p)
    rw [sub_zero, sub_zero, first]
  apply polar_point_eq_of_cos_and_side r _ β _ r_pos length_pos
  · simp only [dist_eq_norm, zero_sub, norm_neg, norm_sub_rev]
  · rw [measured, show β + angle a p z - β = angle a p z by ring]
  · rw [first, det_smul_left] at side
    have signed : 0 ≤ det (direction β) (z - p) := by nlinarith
    rw [show β + angle a p z - β = angle a p z by ring]
    exact mul_nonneg signed (sin_pos_of_pos_of_lt_pi corner_pos corner_small).le

/-- A clockwise triangle fits between its first edge and a lower ray once their gap bounds its apex angle. -/
theorem clockwise_triangle_in_cone (p a z : Plane) (r α β : ℝ) (r_pos : 0 < r)
    (length_pos : 0 < dist p z) (corner_pos : 0 < angle a p z) (corner_small : angle a p z < π)
    (first : a - p = r • direction β) (side : det (a - p) (z - p) ≤ 0)
    (wide_enough : angle a p z ≤ β - α) (width_small : β - α < π) :
    convexHull ℝ ({a, z, p} : Set Plane) ⊆ translatedCone p (direction α) (direction β) := by
  have width_pos : 0 < β - α := corner_pos.trans_le wide_enough
  apply triangle_in_cone_of_corner_vectors
  · rw [first]
    exact smul_mem_twoRayCone r_pos.le (direction_mem_twoRayCone α β β width_pos width_small (by linarith) le_rfl)
  · rw [clockwise_corner_vector p a z r β r_pos length_pos corner_pos corner_small first side]
    exact smul_mem_twoRayCone length_pos.le (direction_mem_twoRayCone α β (β - angle a p z)
      width_pos width_small (by linarith) (by linarith))

theorem counterclockwise_triangle_in_cone (p a z : Plane) (r α β : ℝ) (r_pos : 0 < r)
    (length_pos : 0 < dist p z) (corner_pos : 0 < angle a p z) (corner_small : angle a p z < π)
    (first : a - p = r • direction α) (side : 0 ≤ det (a - p) (z - p))
    (wide_enough : angle a p z ≤ β - α) (width_small : β - α < π) :
    convexHull ℝ ({a, z, p} : Set Plane) ⊆ translatedCone p (direction α) (direction β) := by
  have width_pos : 0 < β - α := corner_pos.trans_le wide_enough
  apply triangle_in_cone_of_corner_vectors
  · rw [first]
    exact smul_mem_twoRayCone r_pos.le (direction_mem_twoRayCone α β α width_pos width_small le_rfl (by linarith))
  · rw [counterclockwise_corner_vector p a z r α r_pos length_pos corner_pos corner_small first side]
    exact smul_mem_twoRayCone length_pos.le (direction_mem_twoRayCone α β (α + angle a p z)
      width_pos width_small (by linarith) (by linarith))

end SixVertexUnfolding
