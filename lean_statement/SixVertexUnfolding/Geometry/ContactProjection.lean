import SixVertexUnfolding.Definitions

/-! The strict projection step in the finite-cut contact argument. -/

namespace SixVertexUnfolding.Contact

/-- If two corners have smaller height than a contained point, the remaining corner has larger height,
unless it is the point itself. -/
theorem triangle_height_strict (height : Plane →ₗ[ℝ] ℝ) (a w q m : Plane)
    (at_a : height a < height m) (at_q : height q < height m)
    (contained : m ∈ convexHull ℝ ({a, w, q} : Set Plane)) (not_w : m ≠ w) : height m < height w := by
  rw [Set.insert_comm a w, convexHull_insert (show ({a, q} : Set Plane).Nonempty from ⟨a, by simp⟩)] at contained
  obtain ⟨z, hz, y, hy, between⟩ := mem_convexJoin.mp contained
  have same : z = w := hz
  subst z
  obtain ⟨s, t, hs, ht, total, expression⟩ := between
  have t_positive : 0 < t := by
    apply lt_of_le_of_ne ht
    intro zero
    have s_one : s = 1 := by linarith
    apply not_w
    rw [← expression, ← zero, s_one, one_smul, zero_smul, add_zero]
  have y_lower : height y < height m := by
    apply convexHull_min _ ((convex_Iio (height m)).linear_preimage height) hy
    rintro p (rfl | rfl)
    exacts [at_a, at_q]
  have measured := congrArg height expression
  simp only [map_add, map_smul, smul_eq_mul] at measured
  have balance := congrArg (fun z : ℝ => z * height m) total
  simp only [add_mul, one_mul] at balance
  by_contra not_larger
  have w_lower := le_of_not_gt not_larger
  nlinarith [mul_nonneg hs (sub_nonneg.mpr w_lower), mul_pos t_positive (sub_pos.mpr y_lower)]

/-- Distinct points at equal positive radius have a strict projection gap, including every earlier point on the second ray. -/
theorem equal_radius_projection (m p : Plane) (m_nonzero : m ≠ 0)
    (equal_radius : ‖p‖ = ‖m‖) (different : m ≠ p)
    (t : ℝ) (lower : 0 ≤ t) (upper : t ≤ 1) : inner ℝ m (t • p) < ‖m‖ ^ 2 := by
  have radius_positive : 0 < ‖m‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr m_nonzero)
  have distance_positive : 0 < ‖m - p‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr different))
  have distance_formula := norm_sub_sq_real m p
  rw [equal_radius] at distance_formula
  have projection_gap : inner ℝ m p < ‖m‖ ^ 2 := by linarith
  rw [inner_smul_right]
  rcases lower.eq_or_lt with zero | positive
  · rw [← zero, zero_mul]
    exact radius_positive
  · exact lt_of_lt_of_le (mul_lt_mul_of_pos_left projection_gap positive)
      (by nlinarith [mul_nonneg (sub_nonneg.mpr upper) radius_positive.le])

/-- The contact containment forces the neighboring source copy beyond the perpendicular projection of the pole. -/
theorem contact_projection_strict (w m p : Plane) (m_nonzero : m ≠ 0)
    (equal_radius : ‖p‖ = ‖m‖) (different : m ≠ p)
    (t : ℝ) (lower : 0 ≤ t) (upper : t ≤ 1)
    (contained : m ∈ convexHull ℝ ({0, w, t • p} : Set Plane)) (not_w : m ≠ w) :
    ‖m‖ ^ 2 < inner ℝ m w := by
  have projection := equal_radius_projection m p m_nonzero equal_radius different t lower upper
  have strict := triangle_height_strict (innerSL ℝ m).toLinearMap 0 w (t • p) m
    (by change inner ℝ m 0 < inner ℝ m m
        rw [inner_zero_right, real_inner_self_eq_norm_sq]
        exact sq_pos_of_pos (norm_pos_iff.mpr m_nonzero))
    (by change inner ℝ m (t • p) < inner ℝ m m
        rwa [real_inner_self_eq_norm_sq]) contained not_w
  change inner ℝ m m < inner ℝ m w at strict
  rwa [real_inner_self_eq_norm_sq] at strict

/-- In squared-distance form, contact forces the original source angle to be obtuse after metric comparison. -/
theorem contact_metric_obtuse (w m p : Plane) (m_nonzero : m ≠ 0)
    (equal_radius : ‖p‖ = ‖m‖) (different : m ≠ p)
    (t : ℝ) (lower : 0 ≤ t) (upper : t ≤ 1)
    (contained : m ∈ convexHull ℝ ({0, w, t • p} : Set Plane)) (not_w : m ≠ w) :
    ‖m‖ ^ 2 + ‖w - m‖ ^ 2 < ‖w‖ ^ 2 := by
  have strict := contact_projection_strict w m p m_nonzero equal_radius different t lower upper contained not_w
  rw [real_inner_comm] at strict
  rw [norm_sub_sq_real]
  linarith

end SixVertexUnfolding.Contact
