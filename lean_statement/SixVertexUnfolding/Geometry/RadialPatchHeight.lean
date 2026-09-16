import SixVertexUnfolding.Geometry.StrictPlanarSectors

/-! A radial four-corner hull inherits strict vertex height away from its pole. -/

namespace SixVertexUnfolding

theorem radial_patch_height_pos (height : Plane →ₗ[ℝ] ℝ) (a b c x : Plane)
    (first : 0 < height a) (second : 0 < height b) (third : 0 < height c)
    (member : x ∈ convexHull ℝ ({0, a, b, c} : Set Plane)) (nonzero : x ≠ 0) : 0 < height x := by
  rw [convexHull_insert (show ({a, b, c} : Set Plane).Nonempty from ⟨a, by simp⟩)] at member
  obtain ⟨z, hz, y, hy, between⟩ := mem_convexJoin.mp member
  have same : z = 0 := hz
  subst z
  obtain ⟨s, t, hs, ht, total, expression⟩ := between
  simp only [smul_zero, zero_add] at expression
  have positive : 0 < t := by
    apply lt_of_le_of_ne ht
    intro zero
    apply nonzero
    rw [← expression, ← zero, zero_smul]
  have y_positive : 0 < height y := by
    apply convexHull_min _ ((convex_Ioi (0 : ℝ)).linear_preimage height) hy
    rintro p (rfl | rfl | rfl)
    exacts [first, second, third]
  rw [← expression, map_smul, smul_eq_mul]
  exact mul_pos positive y_positive

theorem radial_segment_height_pos (height : Plane →ₗ[ℝ] ℝ) (b x : Plane)
    (endpoint : 0 < height b) (member : x ∈ segment ℝ 0 b) (nonzero : x ≠ 0) : 0 < height x := by
  obtain ⟨s, t, hs, ht, total, expression⟩ := member
  simp only [smul_zero, zero_add] at expression
  have positive : 0 < t := by
    apply lt_of_le_of_ne ht
    intro zero
    apply nonzero
    rw [← expression, ← zero, zero_smul]
  rw [← expression, map_smul, smul_eq_mul]
  exact mul_pos positive endpoint

end SixVertexUnfolding
