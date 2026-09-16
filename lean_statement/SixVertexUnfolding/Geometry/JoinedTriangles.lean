import SixVertexUnfolding.Geometry.SegmentCrossing
import SixVertexUnfolding.Geometry.TriangleWeights
import SixVertexUnfolding.Geometry.TriangleHalfplanes

/-! Two triangles on strictly opposite sides of their common base meet exactly along that base. -/

namespace SixVertexUnfolding

/-- The coefficient of the free vertex is exactly the fraction of the signed base height. -/
theorem triangle_weighted_area (a b c x : Plane) (s t u : ℝ)
    (total : s + t + u = 1) (expression : s • a + t • b + u • c = x) :
    det (b - a) (x - a) = u * det (b - a) (c - a) := by
  have base_expression : s • a + t • b + u • c - a = t • (b - a) + u • (c - a) := by
    rw [show s = 1 - t - u by linarith]
    module
  rw [← expression, base_expression, det_add_right, det_smul_right, det_smul_right,
    det_self, mul_zero, zero_add]

/-- No contact outside the retained diagonal is possible, even on triangle boundaries. -/
theorem opposite_triangles_intersection (a b c d : Plane)
    (opposite : det (b - a) (c - a) * det (b - a) (d - a) < 0) :
    convexHull ℝ ({a, b, c} : Set Plane) ∩ convexHull ℝ ({a, b, d} : Set Plane) = segment ℝ a b := by
  apply Set.Subset.antisymm
  · rintro x ⟨left, right⟩
    obtain ⟨s, t, u, hs, ht, hu, total, expression⟩ := triangle_weights a b c x left
    obtain ⟨r, v, z, hr, hv, hz, total', expression'⟩ := triangle_weights a b d x right
    have same := (triangle_weighted_area a b c x s t u total expression).symm.trans
      (triangle_weighted_area a b d x r v z total' expression')
    have zero : u = 0 := by
      rcases mul_neg_iff.mp opposite with ⟨first_pos, second_neg⟩ | ⟨first_neg, second_pos⟩
      · have positive := mul_nonneg hu first_pos.le
        have negative := mul_nonpos_of_nonneg_of_nonpos hz second_neg.le
        nlinarith
      · have negative := mul_nonpos_of_nonneg_of_nonpos hu first_neg.le
        have positive := mul_nonneg hz second_pos.le
        nlinarith
    rw [zero, zero_smul, add_zero] at expression
    exact ⟨s, t, hs, ht, by linarith, expression⟩
  · intro x member
    constructor <;> apply (convex_convexHull ℝ _).segment_subset
      (subset_convexHull ℝ _ (by simp)) (subset_convexHull ℝ _ (by simp)) member

end SixVertexUnfolding
