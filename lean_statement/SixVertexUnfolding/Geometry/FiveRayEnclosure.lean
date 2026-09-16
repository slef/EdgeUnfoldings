import SixVertexUnfolding.Geometry.FiveRaySupportChoice
import SixVertexUnfolding.Geometry.SupportingLineExtension

/-! Construct the enclosing triangle and verify the two corner cuts.
All points stay in the transverse plane, hence in the open hemisphere. -/

namespace SixVertexUnfolding.FiveRayFan

open Set

/-- Extending a segment past its zero-height point reaches positive height. -/
private theorem positive_past_zero (side : Space →ₗ[ℝ] ℝ) {a x b : Space}
    (negative : side a < 0) (zero : side x = 0)
    (between : x ∈ openSegment ℝ a b) : 0 < side b := by
  obtain ⟨s, t, sp, tp, _, combination⟩ := between
  have measured := congrArg side combination
  simp only [map_add, map_smul, smul_eq_mul, zero] at measured
  by_contra h
  have := mul_nonpos_of_nonneg_of_nonpos tp.le (not_lt.mp h)
  nlinarith [mul_neg_of_pos_of_neg sp negative]

/-- An affine line sends intermediate parameters to intermediate points. -/
private theorem line_between (y z : Space) {s t u : ℝ} (st : s ≤ t) (tu : t ≤ u) :
    AffineMap.lineMap y z t ∈
      segment ℝ (AffineMap.lineMap y z s) (AffineMap.lineMap y z u) := by
  rw [← image_segment ℝ (AffineMap.lineMap y z)]
  exact mem_image_of_mem _ (Icc_subset_segment ⟨st, tu⟩)

/-- The chosen opposite supporting line supplies an enclosing triangle.
Its corners are the original first ray and two newly constructed points. -/
theorem enclosing_triangle_of_advances (fan : FiveRayFan)
    (first : fan.side 2 (fan.ray 0) < fan.side 2 (fan.ray 1))
    (last : fan.side 2 (fan.ray 0) < fan.side 2 (fan.ray 4)) :
    ∃ b c : Space, fan.height b = 1 ∧ fan.height c = 1 ∧
      fan.ray 1 ∈ segment ℝ (fan.ray 0) b ∧
      fan.ray 2 ∈ segment ℝ b c ∧
      fan.ray 3 ∈ segment ℝ (fan.ray 2) c ∧
      fan.ray 4 ∈ segment ℝ c (fan.ray 0) := by
  obtain ⟨b, bh, bs, xb⟩ := extend_to_supporting_line fan.height (fan.side 2)
    (fan.ray 0) (fan.ray 1) (fan.level 0) (fan.level 1) first
    (fan.side_strict 2 1 (by decide) (by decide))
  obtain ⟨c, ch, cs, wc⟩ := extend_to_supporting_line fan.height (fan.side 2)
    (fan.ray 0) (fan.ray 4) (fan.level 0) (fan.level 4) last
    (fan.side_strict 2 4 (by decide) (by decide))
  obtain ⟨t, bt⟩ := (fan.rotate 2).first_side_line bh bs
  obtain ⟨u, cu⟩ := (fan.rotate 2).first_side_line ch cs
  change b = AffineMap.lineMap (fan.ray 2) (fan.ray 3) t at bt
  change c = AffineMap.lineMap (fan.ray 2) (fan.ray 3) u at cu
  have b_positive := positive_past_zero (fan.side 1)
    (fan.side_strict 1 0 (by decide) (by decide)) (fan.side_left 1) xb
  have c_positive := positive_past_zero (fan.side 3)
    (fan.side_strict 3 0 (by decide) (by decide)) (fan.side_right 3) wc
  have s12 : fan.side 1 (fan.ray 2) = 0 := fan.side_right 1
  have s13 := fan.side_strict 1 3 (by decide) (by decide)
  have s32 := fan.side_strict 3 2 (by decide) (by decide)
  rw [bt, AffineMap.lineMap_apply_module] at b_positive
  rw [cu, AffineMap.lineMap_apply_module] at c_positive
  simp only [map_add, map_smul, smul_eq_mul, fan.side_left, s12,
    mul_zero, zero_add, add_zero] at b_positive c_positive
  have before : t < 0 := by
    by_contra h
    have := mul_nonpos_of_nonneg_of_nonpos (not_lt.mp h) s13.le
    linarith
  have after : 1 < u := by
    by_contra h
    have := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (not_lt.mp h)) s32.le
    linarith
  refine ⟨b, c, bh, ch, openSegment_subset_segment ℝ _ _ xb, ?_, ?_, ?_⟩
  · rw [bt, cu]
    simpa only [AffineMap.lineMap_apply_zero] using
      line_between (fan.ray 2) (fan.ray 3) before.le (show 0 ≤ u by linarith)
  · rw [cu]
    simpa only [AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] using
      line_between (fan.ray 2) (fan.ray 3) (show (0 : ℝ) ≤ 1 by norm_num) after.le
  · rw [segment_symm]
    exact openSegment_subset_segment ℝ _ _ wc

/-- Every supported five-ray figure is obtained from a triangle by two corner cuts. -/
theorem exists_enclosing_triangle (fan : FiveRayFan) :
    ∃ i : Fin 5, ∃ b c : Space,
      (fan.rotate i).height b = 1 ∧ (fan.rotate i).height c = 1 ∧
      (fan.rotate i).ray 1 ∈ segment ℝ ((fan.rotate i).ray 0) b ∧
      (fan.rotate i).ray 2 ∈ segment ℝ b c ∧
      (fan.rotate i).ray 3 ∈ segment ℝ ((fan.rotate i).ray 2) c ∧
      (fan.rotate i).ray 4 ∈ segment ℝ c ((fan.rotate i).ray 0) := by
  obtain ⟨i, first, last⟩ := fan.exists_enclosing_start
  exact ⟨i, (fan.rotate i).enclosing_triangle_of_advances first last⟩

end SixVertexUnfolding.FiveRayFan
