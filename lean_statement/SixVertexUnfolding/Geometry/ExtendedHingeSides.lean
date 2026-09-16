import SixVertexUnfolding.Geometry.HingeDeterminant

/-! Outwardness depends on the hinge line, including at virtual corners outside the original edge. -/

namespace SixVertexUnfolding

/-- Moving and rescaling the hinge along its line preserves the opposite-side condition. -/
theorem oppositeHingeSides_reanchor (a b c d x y : Plane) (ab : a ≠ b) (cd : c ≠ d)
    (t r : ℝ) (offset : c - a = t • (b - a)) (axis : d - c = r • (b - a)) :
    OppositeHingeSides c d x y ↔ OppositeHingeSides a b x y := by
  have r_ne : r ≠ 0 := by
    intro zero
    rw [zero, zero_smul] at axis
    exact cd (sub_eq_zero.mp axis).symm
  have height (z : Plane) : det (d - c) (z - c) = r * det (b - a) (z - a) := by
    have shifted : z - c = (z - a) - (c - a) := by module
    rw [axis, det_smul_left, shifted, det_sub_right (b - a) (z - a) (c - a),
      offset, det_smul_right, det_self, mul_zero, sub_zero]
  rw [oppositeHingeSides_iff_det c d x y cd, oppositeHingeSides_iff_det a b x y ab,
    height x, height y]
  have factor : 0 < r ^ 2 := sq_pos_of_ne_zero r_ne
  have expression : (r * det (b - a) (x - a)) * (r * det (b - a) (y - a)) =
      r ^ 2 * (det (b - a) (x - a) * det (b - a) (y - a)) := by ring
  rw [expression]
  constructor
  · intro bound
    by_contra positive
    exact (not_lt_of_ge bound) (mul_pos factor (lt_of_not_ge positive))
  · exact mul_nonpos_of_nonneg_of_nonpos factor.le

/-- Any two distinct points on the extended hinge define the same outward-side predicate. -/
theorem oppositeHingeSides_on_same_line (a b c d x y : Plane) (ab : a ≠ b) (cd : c ≠ d)
    (hc : c ∈ affineSpan ℝ ({a, b} : Set Plane)) (hd : d ∈ affineSpan ℝ ({a, b} : Set Plane)) :
    OppositeHingeSides c d x y ↔ OppositeHingeSides a b x y := by
  obtain ⟨t, ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hc
  obtain ⟨u, hu⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hd
  apply oppositeHingeSides_reanchor a b c d x y ab cd t (u - t)
  · rw [← ht, AffineMap.lineMap_apply_module']
    module
  · rw [← ht, ← hu, AffineMap.lineMap_apply_module', AffineMap.lineMap_apply_module']
    module

end SixVertexUnfolding
