import SixVertexUnfolding.Definitions

/-! Elementary Euclidean facts turning exact shortest-path distances into
straight coordinate formulas. No differentiability of the route is assumed. -/

namespace SixVertexUnfolding

open Set

/-- On a straight segment, distance from one endpoint uniquely determines the point. -/
theorem segment_point_unique (a b x y : Plane)
    (hx : x ∈ segment ℝ a b) (hy : y ∈ segment ℝ a b) (same_distance : dist a x = dist a y) : x = y := by
  by_cases same : a = b
  · rw [same, segment_same, mem_singleton_iff] at hx hy
    exact hx.trans hy.symm
  obtain ⟨s, hs, rfl⟩ := mem_segment_iff_wbtw.mp hx
  obtain ⟨t, ht, rfl⟩ := mem_segment_iff_wbtw.mp hy
  rw [dist_left_lineMap, dist_left_lineMap, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hs.1, abs_of_nonneg ht.1] at same_distance
  have equal : s = t := mul_right_cancel₀ (dist_ne_zero.mpr same) same_distance
  rw [equal]

/-- Exact distances proportional to the two subintervals determine the affine interpolation. -/
theorem point_eq_lineMap_of_distance_ratios (a b x : Plane) (s u t L : ℝ)
    (ordered : s < t) (su : s ≤ u) (ut : u ≤ t)
    (first : dist a x = L * (u - s)) (second : dist x b = L * (t - u))
    (whole : dist a b = L * (t - s)) :
    x = AffineMap.lineMap a b ((u - s) / (t - s)) := by
  have denominator : 0 < t - s := sub_pos.mpr ordered
  have coefficient_nonnegative : 0 ≤ (u - s) / (t - s) := div_nonneg (sub_nonneg.mpr su) denominator.le
  have coefficient_le : (u - s) / (t - s) ≤ 1 := (div_le_one denominator).mpr (by linarith)
  have distance_sum : dist a x + dist x b = dist a b := by
    rw [first, second, whole]
    ring
  have between : x ∈ segment ℝ a b := (dist_add_dist_eq_iff.mp distance_sum).mem_segment
  apply segment_point_unique a b x _ between
  · rw [segment_eq_image_lineMap]
    exact ⟨(u - s) / (t - s), ⟨coefficient_nonnegative, coefficient_le⟩, rfl⟩
  · rw [dist_left_lineMap, Real.norm_eq_abs, abs_of_nonneg coefficient_nonnegative, first, whole]
    field_simp [denominator.ne']

/-- Equal half-distances in Euclidean space force the usual midpoint. -/
theorem midpoint_of_half_distances (a b x : Plane) (r : ℝ)
    (first : dist x a = r) (second : dist x b = r) (whole : dist a b = 2 * r) :
    x = midpoint ℝ a b := by
  have identity := EuclideanGeometry.dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq x a b
  rw [first, second, whole] at identity
  apply dist_eq_zero.mp
  nlinarith [dist_nonneg (x := x) (y := midpoint ℝ a b)]

/-- A nonzero interpolation fraction determines the second endpoint from the first and the interpolated point. -/
theorem lineMap_right_unique (a b c : Plane) (r : ℝ) (nonzero : r ≠ 0)
    (same : AffineMap.lineMap a b r = AffineMap.lineMap a c r) : b = c := by
  simp only [AffineMap.lineMap_apply_module] at same
  exact (smul_right_injective (M := Plane) nonzero) (add_left_cancel same)

/-- An interpolation fraction different from one similarly determines the first endpoint. -/
theorem lineMap_left_unique (a b c : Plane) (r : ℝ) (not_one : r ≠ 1)
    (same : AffineMap.lineMap a c r = AffineMap.lineMap b c r) : a = b := by
  simp only [AffineMap.lineMap_apply_module] at same
  exact (smul_right_injective (M := Plane) (sub_ne_zero.mpr not_one.symm)) (add_right_cancel same)

end SixVertexUnfolding
