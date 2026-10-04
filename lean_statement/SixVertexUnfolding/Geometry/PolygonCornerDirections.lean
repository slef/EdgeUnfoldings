import SixVertexUnfolding.Geometry.TriangleCones

/-! A whole polygon's supporting corner cone has the orientation of any
one interior-side witness. This avoids replacing a quadrilateral by a triangle. -/

namespace SixVertexUnfolding

open Real EuclideanGeometry

/-- An affine placement preserves nonnegative corner coordinates. -/
theorem affine_image_corner_cone (place : Plane →ᵃ[ℝ] Plane) (p a z : Plane) :
    place '' translatedCone p (a - p) (z - p) ⊆
      translatedCone (place p) (place a - place p) (place z - place p) := by
  rintro _ ⟨x, ⟨t, u, ht, hu, coords⟩, rfl⟩
  refine ⟨t, u, ht, hu, ?_⟩
  have mapped := congrArg place.linear coords
  have difference (v w : Plane) : place.linear (v - w) = place v - place w :=
    place.linearMap_vsub v w
  simpa only [map_add, map_smul, difference] using mapped

/-- The determinant at a corner can be read at the other end of its edge. -/
theorem corner_determinant_cyclic (a b c : Plane) :
    det (a - c) (b - c) = det (b - a) (c - a) := by
  simp only [det, PiLp.sub_apply]
  ring

/-- One point strictly on the clockwise side fixes the orientation of the full corner cone. -/
theorem clockwise_corner_cone (p a z w : Plane) (r β : ℝ) (r_pos : 0 < r)
    (corner_pos : 0 < angle a p z) (corner_small : angle a p z < π)
    (first : a - p = r • direction β)
    (witness : w ∈ translatedCone p (a - p) (z - p))
    (side : det (a - p) (w - p) < 0) :
    translatedCone p (a - p) (z - p) ⊆
      translatedCone p (direction (β - angle a p z)) (direction β) := by
  obtain ⟨t, u, ht, hu, coords⟩ := witness
  rw [coords, det_add_right, det_smul_right, det_smul_right, det_self, mul_zero, zero_add] at side
  have negative : det (a - p) (z - p) < 0 := by
    by_contra h
    exact (not_lt_of_ge (mul_nonneg hu (le_of_not_gt h))) side
  have length_pos : 0 < dist p z := by
    apply dist_pos.mpr
    intro same
    rw [same, sub_self] at negative
    simp [det] at negative
  have other := clockwise_corner_vector p a z r β r_pos length_pos corner_pos corner_small first negative.le
  rintro x ⟨s, v, hs, hv, position⟩
  refine ⟨v * dist p z, s * r, mul_nonneg hv length_pos.le, mul_nonneg hs r_pos.le, ?_⟩
  rw [position, first, other, mul_smul, mul_smul, add_comm]

/-- The same argument with counterclockwise orientation. -/
theorem counterclockwise_corner_cone (p a z w : Plane) (r β : ℝ) (r_pos : 0 < r)
    (corner_pos : 0 < angle a p z) (corner_small : angle a p z < π)
    (first : a - p = r • direction β)
    (witness : w ∈ translatedCone p (a - p) (z - p))
    (side : 0 < det (a - p) (w - p)) :
    translatedCone p (a - p) (z - p) ⊆
      translatedCone p (direction β) (direction (β + angle a p z)) := by
  obtain ⟨t, u, ht, hu, coords⟩ := witness
  rw [coords, det_add_right, det_smul_right, det_smul_right, det_self, mul_zero, zero_add] at side
  have positive : 0 < det (a - p) (z - p) := by
    by_contra h
    exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hu (le_of_not_gt h))) side
  have length_pos : 0 < dist p z := by
    apply dist_pos.mpr
    intro same
    rw [same, sub_self] at positive
    simp [det] at positive
  have other := counterclockwise_corner_vector p a z r β r_pos length_pos corner_pos corner_small first positive.le
  rintro x ⟨s, v, hs, hv, position⟩
  refine ⟨s * r, v * dist p z, mul_nonneg hs r_pos.le, mul_nonneg hv length_pos.le, ?_⟩
  rw [position, first, other, mul_smul, mul_smul]

end SixVertexUnfolding
