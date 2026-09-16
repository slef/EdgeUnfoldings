import SixVertexUnfolding.Definitions

/-! A continuous affine coordinate that goes from zero to one along one
specified nondegenerate straight segment. -/

namespace SixVertexUnfolding

/-- The normalized scalar projection along an oriented segment. -/
noncomputable def segmentCoordinate (u v x : Space) : ℝ :=
  inner ℝ (v - u) (x - u) / ‖v - u‖ ^ 2

theorem segmentCoordinate_continuous (u v : Space) : Continuous (segmentCoordinate u v) :=
  (continuous_const.inner (continuous_id.sub continuous_const)).div_const _

/-- The coordinate recovers exactly the ordinary line parameter. -/
theorem segmentCoordinate_lineMap (u v : Space) (different : u ≠ v) (t : ℝ) :
    segmentCoordinate u v (AffineMap.lineMap u v t) = t := by
  have norm_ne : ‖v - u‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr different.symm))
  have difference : AffineMap.lineMap u v t - u = t • (v - u) := by
    rw [AffineMap.lineMap_apply_module]
    module
  unfold segmentCoordinate
  rw [difference, inner_smul_right, real_inner_self_eq_norm_sq]
  exact mul_div_cancel_right₀ t norm_ne

theorem segmentCoordinate_left (u v : Space) (different : u ≠ v) : segmentCoordinate u v u = 0 := by
  simpa only [AffineMap.lineMap_apply_zero] using segmentCoordinate_lineMap u v different 0

theorem segmentCoordinate_right (u v : Space) (different : u ≠ v) : segmentCoordinate u v v = 1 := by
  simpa only [AffineMap.lineMap_apply_one] using segmentCoordinate_lineMap u v different 1

end SixVertexUnfolding
