import SixVertexUnfolding.Geometry.CircularGapData
import Mathlib.Algebra.BigOperators.Fin

/-! Index the circular gaps without duplicating the closing direction.
Their widths telescope to one full turn. -/

namespace SixVertexUnfolding

open Real Set
open scoped BigOperators

/-- The next source angle, lifted by one turn at the last source. -/
noncomputable def circularGapEnd {n : ℕ} (θ : Fin n → ℝ) (first i : Fin n) : ℝ :=
  if h : i.val + 1 < n then θ ⟨i.val + 1, h⟩ else θ first + 2 * π

theorem circularGapEnd_gap {n : ℕ} (θ : Fin n → ℝ) (first last i : Fin n)
    (at_last : last.val + 1 = n) :
    IsCircularGap θ first last (θ i) (circularGapEnd θ first i) := by
  unfold circularGapEnd
  split_ifs with next
  · exact Or.inl ⟨i, ⟨i.val + 1, next⟩, rfl, rfl, rfl⟩
  · have equal : i = last := Fin.ext (by omega)
    exact Or.inr ⟨congrArg θ equal, rfl⟩

/-- Every gap has one index, namely its first source. -/
theorem circularGapEnd_exhaustive {n : ℕ} (θ : Fin n → ℝ) (first last : Fin n)
    (at_last : last.val + 1 = n) {α β : ℝ} (gap : IsCircularGap θ first last α β) :
    ∃ i, α = θ i ∧ β = circularGapEnd θ first i := by
  rcases gap with ⟨i, j, next, rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨i, rfl, ?_⟩
    have inside : i.val + 1 < n := by omega
    simp only [circularGapEnd, dif_pos inside]
    congr 1
    exact Fin.ext next
  · exact ⟨last, rfl, by simp [circularGapEnd, at_last]⟩

/-- Adding all consecutive widths, including the closing gap, gives exactly one turn. -/
theorem sum_circularGap_widths {n : ℕ} (θ : Fin n → ℝ) (first : Fin n)
    (at_first : first.val = 0) :
    ∑ i, (circularGapEnd θ first i - θ i) = 2 * π := by
  cases n with
  | zero => exact Fin.elim0 first
  | succ n =>
    have equal : first = 0 := Fin.ext at_first
    subst first
    have ordinary (i : Fin n) : circularGapEnd θ 0 i.castSucc = θ i.succ := by
      simp only [circularGapEnd, Fin.val_castSucc, dif_pos (Nat.succ_lt_succ i.isLt)]
      rfl
    have closing : circularGapEnd θ 0 (Fin.last n) = θ 0 + 2 * π := by
      simp [circularGapEnd]
    rw [Finset.sum_sub_distrib, Fin.sum_univ_castSucc]
    simp only [ordinary, closing]
    rw [Fin.sum_univ_succ]
    ring

/-- Distinct gaps have distinct midpoints; their order is the source order. -/
theorem circularGapMidpoint_strictMono {n : ℕ} (θ : Fin n → ℝ)
    (increasing : StrictMono θ) (bounds : ∀ i, 0 ≤ θ i ∧ θ i < 2 * π)
    (first : Fin n) :
    StrictMono (fun i => (θ i + circularGapEnd θ first i) / 2) := by
  intro i j before
  have next : i.val + 1 < n := by omega
  have left : circularGapEnd θ first i ≤ θ j := by
    rw [circularGapEnd, dif_pos next]
    exact increasing.monotone (by change i.val + 1 ≤ j.val; omega)
  have right : θ j < circularGapEnd θ first j := by
    unfold circularGapEnd
    split_ifs with after
    · exact increasing (by change j.val < j.val + 1; omega)
    · linarith [(bounds j).2, (bounds first).1]
  linarith [increasing before]

/-- The gap indices give exactly the previously constructed cut directions. -/
noncomputable def circularGapMidpointEquiv {n : ℕ} (θ : Fin n → ℝ)
    (increasing : StrictMono θ) (bounds : ∀ i, 0 ≤ θ i ∧ θ i < 2 * π)
    (first last : Fin n) (at_last : last.val + 1 = n) :
    Fin n ≃ circularGapMidpoints θ first last :=
  Equiv.ofBijective
    (fun i => ⟨(θ i + circularGapEnd θ first i) / 2,
      (mem_circularGapMidpoints_iff θ first last _).mpr
        ⟨_, _, circularGapEnd_gap θ first last i at_last, rfl⟩⟩)
    ⟨fun i j equal => (circularGapMidpoint_strictMono θ increasing bounds first).injective
        (congrArg Subtype.val equal), by
      intro m
      obtain ⟨α, β, gap, midpoint⟩ := (mem_circularGapMidpoints_iff θ first last m).mp m.property
      obtain ⟨i, rfl, rfl⟩ := circularGapEnd_exhaustive θ first last at_last gap
      exact ⟨i, Subtype.ext midpoint.symm⟩⟩

end SixVertexUnfolding
