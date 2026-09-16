import SixVertexUnfolding.Geometry.MetricSegmentCoordinates

/-! Two consecutive straight pieces with the same speed have the same
velocity vector. This turns local straight crossings into a global line. -/

namespace SixVertexUnfolding

/-- Collinear pieces whose lengths are speed times duration have equal velocities. -/
theorem straight_pieces_equal_velocity (p q r : Plane) (h k L : ℝ)
    (h_pos : 0 < h) (k_pos : 0 < k) (between : Wbtw ℝ p q r)
    (first : dist p q = L * h) (second : dist q r = L * k) :
    h⁻¹ • (q - p) = k⁻¹ • (r - q) := by
  have sum : dist p q + dist q r = dist p r := dist_add_dist_eq_iff.mpr between
  have expression := point_eq_lineMap_of_distance_ratios p r q 0 h (h + k) L
    (by linarith) h_pos.le (by linarith) (by simpa only [sub_zero] using first)
    (by simpa only [add_sub_cancel_left] using second)
    (by rw [sub_zero]; rw [first, second] at sum; linarith)
  simp only [sub_zero, AffineMap.lineMap_apply_module'] at expression
  have scaled : (h + k) • (q - p) = h • (r - p) := by
    rw [expression, add_sub_cancel_right, smul_smul,
      mul_div_cancel₀ h (ne_of_gt (add_pos h_pos k_pos))]
  have balance : k • (q - p) = h • (r - q) := by
    calc
      k • (q - p) = (h + k) • (q - p) - h • (q - p) := by module
      _ = h • (r - p) - h • (q - p) := by rw [scaled]
      _ = h • (r - q) := by module
  have left_scale : (h * k)⁻¹ * k = h⁻¹ := by field_simp
  have right_scale : (h * k)⁻¹ * h = k⁻¹ := by field_simp
  simpa only [smul_smul, left_scale, right_scale] using congrArg (fun x : Plane => (h * k)⁻¹ • x) balance

end SixVertexUnfolding
