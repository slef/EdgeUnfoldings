import SixVertexUnfolding.Geometry.PolarArcs
import Mathlib.Data.Finset.Sort

/-! Distinct source copies on a common circle admit a strictly increasing
angular enumeration in one full turn. The last-to-first gap is left explicit.
-/

namespace SixVertexUnfolding

open Real Set

/-- Every point on a positive-radius circle has an angle in a half-open full turn. -/
theorem circle_point_angle {z p : Plane} {R : ℝ} (positive : 0 < R)
    (radius : dist p z = R) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ < 2 * π ∧ p = z + R • direction θ := by
  have nonzero : p - z ≠ 0 := by
    intro zero
    have same := sub_eq_zero.mp zero
    rw [same, dist_self] at radius
    linarith
  have norm : dist (0 : Plane) (p - z) = R := by
    rw [dist_zero_left, ← dist_eq_norm, radius]
  obtain ⟨θ, low, high, coordinates⟩ := polar_representation_in_turn 0 (p - z) nonzero
  rw [norm] at coordinates
  by_cases endpoint : θ = 2 * π
  · refine ⟨0, le_rfl, by positivity, ?_⟩
    rw [endpoint, show 2 * π = 0 + 2 * π by ring, direction_add_two_pi] at coordinates
    exact eq_add_of_sub_eq' coordinates
  · exact ⟨θ, low, lt_of_le_of_ne (by simpa using high) endpoint,
      eq_add_of_sub_eq' coordinates⟩

/-- A finite set of distinct source copies is enumerated in genuine angular order. -/
theorem exists_circular_source_order (sources : Set Plane) (finite : sources.Finite)
    (z : Plane) (R : ℝ) (positive : 0 < R)
    (radius : ∀ p ∈ sources, dist p z = R) :
    ∃ e : Fin sources.ncard ≃ sources, ∃ θ : Fin sources.ncard → ℝ,
      StrictMono θ ∧ (∀ i, 0 ≤ θ i ∧ θ i < 2 * π) ∧
      ∀ i, (e i : Plane) = z + R • direction (θ i) := by
  classical
  have angles (p : sources) := circle_point_angle positive (radius p p.property)
  choose angle low high coordinates using angles
  have injective : Function.Injective angle := by
    intro p q same
    apply Subtype.ext
    rw [coordinates p, coordinates q, same]
  letI : LinearOrder sources := LinearOrder.lift' angle injective
  letI := finite.fintype
  let e : Fin sources.ncard ≃o sources :=
    Fintype.orderIsoFinOfCardEq sources (by exact Nat.card_eq_fintype_card.symm)
  refine ⟨e.toEquiv, fun i => angle (e i), ?_, fun i => ⟨low (e i), high (e i)⟩,
    fun i => coordinates (e i)⟩
  intro i j order
  exact e.strictMono order

/-- Consecutive entries leave no source in the open angular gap between them.
Sources preceding the gap are represented one turn later. -/
theorem circular_order_gap {sources : Set Plane} {n : ℕ} (e : Fin n ≃ sources)
    (θ : Fin n → ℝ) (increasing : StrictMono θ)
    (bounds : ∀ i, 0 ≤ θ i ∧ θ i < 2 * π) (z : Plane) (R : ℝ)
    (position : ∀ i, (e i : Plane) = z + R • direction (θ i))
    (i j : Fin n) (next : j.val = i.val + 1) :
    ∀ p ∈ sources, ∃ φ ∈ Icc (θ j) (θ i + 2 * π), p = z + R • direction φ := by
  intro p hp
  let k := e.symm ⟨p, hp⟩
  have represented : p = z + R • direction (θ k) :=
    (congrArg Subtype.val (e.apply_symm_apply ⟨p, hp⟩)).symm.trans (position k)
  by_cases before : k ≤ i
  · refine ⟨θ k + 2 * π, ⟨by linarith [(bounds j).2, (bounds k).1],
      by linarith [increasing.monotone before]⟩, ?_⟩
    rwa [direction_add_two_pi]
  · have after : j ≤ k := by omega
    exact ⟨θ k, ⟨increasing.monotone after, by linarith [(bounds k).2, (bounds i).1]⟩,
      represented⟩

/-- The final-to-first gap has the same property, using the next full turn. -/
theorem closing_circular_order_gap {sources : Set Plane} {n : ℕ} (e : Fin n ≃ sources)
    (θ : Fin n → ℝ) (increasing : StrictMono θ)
    (z : Plane) (R : ℝ) (position : ∀ i, (e i : Plane) = z + R • direction (θ i))
    (first last : Fin n) (at_first : first.val = 0) (at_last : last.val + 1 = n) :
    ∀ p ∈ sources, ∃ φ ∈ Icc (θ first + 2 * π) (θ last + 2 * π),
      p = z + R • direction φ := by
  intro p hp
  let k := e.symm ⟨p, hp⟩
  have represented : p = z + R • direction (θ k) :=
    (congrArg Subtype.val (e.apply_symm_apply ⟨p, hp⟩)).symm.trans (position k)
  refine ⟨θ k + 2 * π, ⟨?_, ?_⟩, by rwa [direction_add_two_pi]⟩
  · linarith [increasing.monotone (show first ≤ k by omega)]
  · linarith [increasing.monotone (show k ≤ last by omega)]

/-- Between two entries of an increasing finite list, some consecutive pair brackets the angle. -/
theorem consecutive_angles_cover {n : ℕ} (θ : Fin n → ℝ) (increasing : StrictMono θ)
    (first last : Fin n) {φ : ℝ} (after_first : θ first ≤ φ) (before_last : φ < θ last) :
    ∃ i j : Fin n, j.val = i.val + 1 ∧ φ ∈ Icc (θ i) (θ j) := by
  classical
  let s := Finset.univ.filter (fun i => θ i ≤ φ)
  have nonempty : s.Nonempty := ⟨first, Finset.mem_filter.mpr ⟨Finset.mem_univ _, after_first⟩⟩
  let i := s.max' nonempty
  have below : θ i ≤ φ := (Finset.mem_filter.mp (Finset.max'_mem s nonempty)).2
  have earlier : i < last := by
    by_contra reversed
    have := increasing.monotone (le_of_not_gt reversed)
    linarith
  have has_next : i.val + 1 < n := by omega
  let j : Fin n := ⟨i.val + 1, has_next⟩
  refine ⟨i, j, rfl, below, ?_⟩
  by_contra above
  have member : j ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, (lt_of_not_ge above).le⟩
  have maximum : j ≤ i := Finset.le_max' s j member
  have values : i.val + 1 ≤ i.val := maximum
  omega

/-- Every direction lies in an ordinary gap or in the closing gap, possibly
using the representative one turn later. -/
theorem circular_gaps_cover_direction {n : ℕ} (θ : Fin n → ℝ) (increasing : StrictMono θ)
    (bounds : ∀ i, 0 ≤ θ i ∧ θ i < 2 * π) (first last : Fin n)
    {φ : ℝ} (in_turn : φ ∈ Ico 0 (2 * π)) :
    (∃ i j : Fin n, j.val = i.val + 1 ∧ φ ∈ Icc (θ i) (θ j)) ∨
      ∃ ψ ∈ Icc (θ last) (θ first + 2 * π), direction φ = direction ψ := by
  by_cases after_first : θ first ≤ φ
  · by_cases before_last : φ < θ last
    · exact Or.inl (consecutive_angles_cover θ increasing first last after_first before_last)
    · exact Or.inr ⟨φ, ⟨le_of_not_gt before_last, by linarith [in_turn.2, (bounds first).1]⟩, rfl⟩
  · refine Or.inr ⟨φ + 2 * π,
      ⟨by linarith [in_turn.1, (bounds last).2], by linarith⟩, ?_⟩
    exact (direction_add_two_pi φ).symm

end SixVertexUnfolding
