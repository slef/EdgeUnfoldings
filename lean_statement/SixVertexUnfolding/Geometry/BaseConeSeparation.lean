import SixVertexUnfolding.Geometry.TwoRayCones

/-! The second opposite-petal case, including a closed sector of width exactly pi. -/

namespace SixVertexUnfolding

open Real

/-- A closed sector of width at most pi that avoids angle zero admits a strict separator from the positive horizontal ray. -/
theorem sector_separator_from_zero (a b : ℝ) (start_pos : 0 < a) (end_small : b < 2 * π)
    (_ordered : a ≤ b) (width : b - a ≤ π) :
    ∃ θ : ℝ, 0 < θ ∧ θ < π ∧ θ ≤ a ∧ b ≤ θ + π := by
  let lo := max 0 (b - π)
  let hi := min π a
  have lo_le_hi : lo ≤ hi := max_le (le_min pi_pos.le start_pos.le)
    (le_min (by linarith) (by linarith))
  have hi_pos : 0 < hi := lt_min pi_pos start_pos
  have lo_small : lo < π := max_lt pi_pos (by linarith)
  refine ⟨(lo + hi) / 2, ?_, ?_, ?_, ?_⟩
  · have := le_max_left (0 : ℝ) (b - π)
    change 0 ≤ lo at this
    linarith
  · have := min_le_left π a
    change hi ≤ π at this
    linarith
  · have := min_le_right π a
    change hi ≤ a at this
    linarith
  · have := le_max_right (0 : ℝ) (b - π)
    change b - π ≤ lo at this
    linarith

/-- A height nonnegative on all four cone rays and negative on the base displacement excludes a meeting. -/
theorem opposed_cones_disjoint_of_height (p q e f g h : Plane) (height : Plane →ₗ[ℝ] ℝ)
    (base_negative : height (q - p) < 0)
    (he : 0 ≤ height e) (hf : 0 ≤ height f) (hg : 0 ≤ height g) (hh : 0 ≤ height h) :
    Disjoint (translatedCone p e f) (translatedCone q (-g) (-h)) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨a, b, ha, hb, first⟩ ⟨c, d, hc, hd, second⟩
  have displacement : q - p = a • e + b • f + c • g + d • h := by
    calc
      q - p = (x - p) - (x - q) := by module
      _ = a • e + b • f + c • g + d • h := by rw [first, second]; module
  rw [displacement, map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul] at base_negative
  change a * height e + b * height f + c * height g + d * height h < 0 at base_negative
  linarith [mul_nonneg ha he, mul_nonneg hb hf, mul_nonneg hc hg, mul_nonneg hd hh]

/-- The four angle-sum bounds place both base cones in one closed half-plane excluding their positive base displacement. -/
theorem base_cones_disjoint (base α β σ τ : ℝ)
    (base_pos : 0 < base) (α_pos : 0 < α) (β_pos : 0 < β) (σ_pos : 0 < σ) (τ_pos : 0 < τ)
    (left_nonempty : α + σ ≤ 2 * π) (_right_nonempty : β + τ ≤ 2 * π)
    (left_sum : π ≤ α + σ) (right_sum : π ≤ β + τ)
    (outer_sum : π ≤ α + β) (fan_sum : π ≤ σ + τ) :
    Disjoint (translatedCone 0 (direction α) (direction (2 * π - σ)))
      (translatedCone (base • direction 0) (-direction τ) (-direction (2 * π - β))) := by
  let a := min α τ
  let b := 2 * π - min σ β
  have start_pos : 0 < a := lt_min α_pos τ_pos
  have end_small : b < 2 * π := by have := lt_min σ_pos β_pos; dsimp [b]; linarith
  have ordered : a ≤ b := by
    have first := min_le_left α τ
    have second := min_le_left σ β
    dsimp [a, b]
    linarith
  have width : b - a ≤ π := by
    dsimp [a, b]
    rcases le_total α τ with first | first <;> rcases le_total σ β with second | second
    · rw [min_eq_left first, min_eq_left second]; linarith
    · rw [min_eq_left first, min_eq_right second]; linarith
    · rw [min_eq_right first, min_eq_left second]; linarith
    · rw [min_eq_right first, min_eq_right second]; linarith
  obtain ⟨θ, θ_pos, θ_small, start, finish⟩ := sector_separator_from_zero a b start_pos end_small ordered width
  have ray_nonnegative (x : ℝ) (lo : a ≤ x) (hi : x ≤ b) : 0 ≤ det (direction θ) (direction x) := by
    rw [direction_det]
    apply sin_nonneg_of_nonneg_of_le_pi <;> linarith
  have left_start : a ≤ α := min_le_left _ _
  have right_start : a ≤ τ := min_le_right _ _
  have left_end : 2 * π - σ ≤ b := by dsimp [b]; linarith [min_le_left σ β]
  have right_end : 2 * π - β ≤ b := by dsimp [b]; linarith [min_le_right σ β]
  have left_order : α ≤ 2 * π - σ := by linarith
  have right_order : τ ≤ 2 * π - β := by linarith
  apply opposed_cones_disjoint_of_height 0 (base • direction 0) _ _ _ _ (detHeight (direction θ)).toLinearMap
  · change det (direction θ) (base • direction 0 - 0) < 0
    rw [sub_zero, det_smul_right, direction_det]
    exact mul_neg_of_pos_of_neg base_pos (sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith))
  · exact ray_nonnegative α left_start (left_order.trans left_end)
  · exact ray_nonnegative _ (left_start.trans left_order) left_end
  · exact ray_nonnegative τ right_start (right_order.trans right_end)
  · exact ray_nonnegative _ (right_start.trans right_order) right_end

end SixVertexUnfolding
