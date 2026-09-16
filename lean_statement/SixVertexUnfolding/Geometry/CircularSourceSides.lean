import SixVertexUnfolding.Geometry.CircularGapSum

/-! The gap immediately before a source lies on one side of its ray;
the gap immediately after it lies on the other, including the closing gap. -/

namespace SixVertexUnfolding

open Set Real

variable {n : ℕ} (θ : Fin n → ℝ) (increasing : StrictMono θ)
    (bounds : ∀ i, 0 ≤ θ i ∧ θ i < 2 * π) (first last : Fin n)
    (at_first : first.val = 0) (at_last : last.val + 1 = n) (two : first < last)

include increasing bounds at_last two

theorem circularGapEnd_bounds (i : Fin n) :
    θ i < circularGapEnd θ first i ∧ circularGapEnd θ first i < θ i + 2 * π := by
  unfold circularGapEnd
  split_ifs with next
  · exact ⟨increasing (by change i.val < i.val + 1; omega),
      by linarith [(bounds ⟨i.val + 1, next⟩).2, (bounds i).1]⟩
  · have same : i = last := Fin.ext (by omega)
    subst i
    exact ⟨by linarith [(bounds last).2, (bounds first).1], by linarith [increasing two]⟩

/-- The outgoing gap midpoint is strictly to the positive side of its source ray. -/
theorem circularGapMidpoint_after (i : Fin n) :
    0 < sin ((θ i + circularGapEnd θ first i) / 2 - θ i) := by
  obtain ⟨positive, width⟩ := circularGapEnd_bounds θ increasing bounds first last at_last two i
  exact sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)

include at_first in
/-- The incoming gap has the same source at its far endpoint and lies strictly on the negative side. -/
theorem exists_circularGap_before (i : Fin n) :
    ∃ j : Fin n, direction (circularGapEnd θ first j) = direction (θ i) ∧
      sin ((θ j + circularGapEnd θ first j) / 2 - θ i) < 0 := by
  by_cases positive : 0 < i.val
  · let j : Fin n := ⟨i.val - 1, by omega⟩
    have next : j.val + 1 < n := by dsimp [j]; omega
    have end_eq : circularGapEnd θ first j = θ i := by
      rw [circularGapEnd, dif_pos next]
      congr 1
      apply Fin.ext
      dsimp [j]
      omega
    refine ⟨j, congrArg direction end_eq, ?_⟩
    obtain ⟨ordered, width⟩ := circularGapEnd_bounds θ increasing bounds first last at_last two j
    rw [end_eq] at ordered width ⊢
    rw [show (θ j + θ i) / 2 - θ i = -((θ i - θ j) / 2) by ring, sin_neg]
    exact neg_neg_of_pos (sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
  · have same : i = first := Fin.ext (by omega)
    subst i
    have end_eq : circularGapEnd θ first last = θ first + 2 * π := by
      simp [circularGapEnd, at_last]
    refine ⟨last, ?_, ?_⟩
    · rw [end_eq, direction_add_two_pi]
    · obtain ⟨ordered, width⟩ := circularGapEnd_bounds θ increasing bounds first last at_last two last
      rw [end_eq] at ordered width ⊢
      rw [show (θ last + (θ first + 2 * π)) / 2 - θ first =
        -((θ first + 2 * π - θ last) / 2) + 2 * π by ring, sin_add_two_pi, sin_neg]
      exact neg_neg_of_pos (sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))

end SixVertexUnfolding
