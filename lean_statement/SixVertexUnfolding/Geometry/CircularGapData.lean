import SixVertexUnfolding.Geometry.CircularVoronoiRays

/-! Recover the two endpoint angles and the empty-gap property from any
member of the finite list of cut directions, including its closing gap.
-/

namespace SixVertexUnfolding

open Real Set

/-- An ordinary consecutive gap or the last-to-first gap, in one full turn. -/
def IsCircularGap {n : ℕ} (θ : Fin n → ℝ) (first last : Fin n) (α β : ℝ) : Prop :=
  (∃ i j : Fin n, j.val = i.val + 1 ∧ α = θ i ∧ β = θ j) ∨
    (α = θ last ∧ β = θ first + 2 * π)

/-- The midpoint list and the explicit gap list describe the same directions. -/
theorem mem_circularGapMidpoints_iff {n : ℕ} (θ : Fin n → ℝ) (first last : Fin n) (m : ℝ) :
    m ∈ circularGapMidpoints θ first last ↔
      ∃ α β, IsCircularGap θ first last α β ∧ m = (α + β) / 2 := by
  constructor
  · rintro (⟨i, j, next, midpoint⟩ | midpoint)
    · exact ⟨θ i, θ j, Or.inl ⟨i, j, next, rfl, rfl⟩, midpoint⟩
    · exact ⟨θ last, θ first + 2 * π, Or.inr ⟨rfl, rfl⟩, midpoint⟩
  · rintro ⟨α, β, (⟨i, j, next, rfl, rfl⟩ | ⟨rfl, rfl⟩), midpoint⟩
    · exact Or.inl ⟨i, j, next, midpoint⟩
    · exact Or.inr midpoint

/-- Earlier gap midpoints give disjoint ordered gap intervals, including
when the later interval crosses the angular cut. -/
theorem circular_gaps_separated {n : ℕ} (θ : Fin n → ℝ) (increasing : StrictMono θ)
    (bounds : ∀ i, 0 ≤ θ i ∧ θ i < 2 * π) (first last : Fin n)
    (at_first : first.val = 0) (at_last : last.val + 1 = n)
    {α β γ δ : ℝ} (left : IsCircularGap θ first last α β)
    (right : IsCircularGap θ first last γ δ) (ordered : (α + β) / 2 < (γ + δ) / 2) :
    β ≤ γ ∧ δ ≤ α + 2 * π := by
  rcases left with ⟨i, j, next, rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases right with ⟨k, l, after, rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have before : j ≤ k := by
      by_contra wrong
      have ki : k ≤ i := by omega
      have lj : l ≤ j := by omega
      linarith [increasing.monotone ki, increasing.monotone lj]
    exact ⟨increasing.monotone before, by linarith [(bounds l).2, (bounds i).1]⟩
  · exact ⟨increasing.monotone (by omega), by linarith [increasing.monotone (show first ≤ i by omega)]⟩
  · have k_last := increasing.monotone (show k ≤ last by omega)
    have l_last := increasing.monotone (show l ≤ last by omega)
    linarith [(bounds last).2, (bounds first).1]
  · linarith

/-- An explicit listed gap has its two source endpoints and no intervening
source copy; all angles are bounded in one turn from the first source. -/
theorem circular_gap_spec {sources : Set Plane} {n : ℕ} (sites : Fin n ≃ sources)
    (θ : Fin n → ℝ) (increasing : StrictMono θ) (bounds : ∀ i, 0 ≤ θ i ∧ θ i < 2 * π)
    (z : Plane) (R : ℝ) (position : ∀ i, (sites i : Plane) = z + R • direction (θ i))
    (first last : Fin n) (at_first : first.val = 0) (at_last : last.val + 1 = n)
    (two : first < last) {α β : ℝ} (gap : IsCircularGap θ first last α β) :
    α < β ∧ β < α + 2 * π ∧ θ first ≤ α ∧ β ≤ θ first + 2 * π ∧
      z + R • direction α ∈ sources ∧ z + R • direction β ∈ sources ∧
      ∀ p ∈ sources, ∃ φ ∈ Icc β (α + 2 * π), p = z + R • direction φ := by
  rcases gap with ⟨i, j, next, rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨increasing (by omega), ?_, increasing.monotone (by omega), ?_,
      position i ▸ (sites i).property, position j ▸ (sites j).property,
      circular_order_gap sites θ increasing bounds z R position i j next⟩
    · linarith [(bounds i).1, (bounds j).2]
    · linarith [(bounds j).2, (bounds first).1]
  · refine ⟨?_, ?_, increasing.monotone two.le, le_rfl,
      position last ▸ (sites last).property, ?_,
      closing_circular_order_gap sites θ increasing z R position first last at_first at_last⟩
    · linarith [(bounds last).2, (bounds first).1]
    · linarith [increasing two]
    · rw [direction_add_two_pi]
      exact position first ▸ (sites first).property

/-- Each listed midpoint comes from an actual empty source gap in one turn. -/
theorem circular_midpoint_gap {sources : Set Plane} {n : ℕ} (sites : Fin n ≃ sources)
    (θ : Fin n → ℝ) (increasing : StrictMono θ) (bounds : ∀ i, 0 ≤ θ i ∧ θ i < 2 * π)
    (z : Plane) (R : ℝ) (position : ∀ i, (sites i : Plane) = z + R • direction (θ i))
    (first last : Fin n) (at_first : first.val = 0) (at_last : last.val + 1 = n)
    (two : first < last) {m : ℝ} (member : m ∈ circularGapMidpoints θ first last) :
    ∃ α β : ℝ, α < β ∧ β < α + 2 * π ∧ m = (α + β) / 2 ∧
      θ first ≤ α ∧ β ≤ θ first + 2 * π ∧
      z + R • direction α ∈ sources ∧ z + R • direction β ∈ sources ∧
      ∀ p ∈ sources, ∃ φ ∈ Icc β (α + 2 * π), p = z + R • direction φ := by
  obtain ⟨α, β, gap, midpoint⟩ := (mem_circularGapMidpoints_iff θ first last m).mp member
  obtain ⟨ordered, width, low, high, first_source, second_source, empty_gap⟩ :=
    circular_gap_spec sites θ increasing bounds z R position first last at_first at_last two gap
  exact ⟨α, β, ordered, width, midpoint, low, high, first_source, second_source, empty_gap⟩

end SixVertexUnfolding
