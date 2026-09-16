import SixVertexUnfolding.Geometry.SphericalSpan

/-! Angular diameter of a segment whose rays have positive height. -/

namespace SixVertexUnfolding

open InnerProductGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Two points on one segment can be ordered from its first endpoint. -/
theorem segment_points_ordered (a b x y : E)
    (hx : x ∈ segment ℝ a b) (hy : y ∈ segment ℝ a b) :
    x ∈ segment ℝ a y ∨ y ∈ segment ℝ a x := by
  rw [segment_eq_image_lineMap] at hx hy
  obtain ⟨s, hs, rfl⟩ := hx
  obtain ⟨t, ht, rfl⟩ := hy
  rcases le_total s t with ordered | ordered
  · left
    have between := (Wbtw.of_le_of_le hs.1 ordered).map (AffineMap.lineMap a b)
    simpa only [AffineMap.lineMap_apply_zero] using mem_segment_iff_wbtw.mpr between
  · right
    have between := (Wbtw.of_le_of_le ht.1 ordered).map (AffineMap.lineMap a b)
    simpa only [AffineMap.lineMap_apply_zero] using mem_segment_iff_wbtw.mpr between

/-- A subsegment has no larger angular diameter than the whole segment. -/
theorem angle_le_of_segment_points (height : E →ₗ[ℝ] ℝ) (a b x y : E)
    (ha : 0 < height a) (hb : 0 < height b)
    (hx : x ∈ segment ℝ a b) (hy : y ∈ segment ℝ a b) :
    angle x y ≤ angle a b := by
  have positive (z : E) (member : z ∈ segment ℝ a b) : 0 < height z := by
    obtain ⟨s, t, hs, ht, total, combination⟩ := member
    rw [← combination, map_add, map_smul, map_smul]
    change 0 < s * height a + t * height b
    by_cases s_pos : 0 < s
    · exact add_pos_of_pos_of_nonneg (mul_pos s_pos ha) (mul_nonneg ht hb.le)
    · have t_pos : 0 < t := by linarith
      exact add_pos_of_nonneg_of_pos (mul_nonneg hs ha.le) (mul_pos t_pos hb)
  have x_ne : x ≠ 0 := by intro zero; have := positive x hx; simpa [zero] using this
  have y_ne : y ≠ 0 := by intro zero; have := positive y hy; simpa [zero] using this
  rcases segment_points_ordered a b x y hx hy with first | second
  · have whole := angle_add_of_segment a b y y_ne hy
    have part := angle_add_of_segment a y x x_ne first
    linarith [angle_nonneg a x, angle_nonneg y b]
  · have whole := angle_add_of_segment a b x x_ne hx
    have part := angle_add_of_segment a x y y_ne second
    linarith [angle_nonneg a y, angle_nonneg x b, angle_comm y x]

end SixVertexUnfolding
