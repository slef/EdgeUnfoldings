import SixVertexUnfolding.Definitions

/-! A continuous function selecting from finitely many continuous formulas
cannot change formula near a point where those values are distinct. -/

namespace SixVertexUnfolding

open Set Filter
open scoped Topology

variable {X ι : Type*} [TopologicalSpace X] [Finite ι]

/-- Distinct candidate values force a locally fixed choice, including on a relative domain. -/
theorem continuous_finite_choice_local (S : Set X) (f : X → ℝ) (g : ι → X → ℝ)
    (continuous_f : ContinuousOn f S) (continuous_g : ∀ i, ContinuousOn (g i) S)
    (selected : ∀ x ∈ S, ∃ i, f x = g i x) (x : X) (hx : x ∈ S) (i : ι)
    (at_x : f x = g i x) (separated : ∀ j, j ≠ i → g i x ≠ g j x) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U ∩ S, f y = g i y := by
  have excluded (j : ι) (different : j ≠ i) : ∀ᶠ y in 𝓝[S] x, f y ≠ g j y := by
    have difference := (continuous_f x hx).sub (continuous_g j x hx)
    have nonzero : f x - g j x ≠ 0 := sub_ne_zero.mpr (at_x ▸ separated j different)
    simpa only [sub_ne_zero] using difference.tendsto.eventually_ne nonzero
  have all : ∀ᶠ y in 𝓝[S] x, ∀ j, j ≠ i → f y ≠ g j y := by
    apply eventually_all.mpr
    intro j
    by_cases different : j ≠ i
    · exact (excluded j different).mono (fun _ h _ => h)
    · exact Eventually.of_forall (fun _ impossible => (different impossible).elim)
  have equal : ∀ᶠ y in 𝓝[S] x, f y = g i y := by
    filter_upwards [all, self_mem_nhdsWithin] with y hy member
    obtain ⟨j, hj⟩ := selected y member
    by_cases same : j = i
    · exact same ▸ hj
    · exact (hy j same hj).elim
  exact mem_nhdsWithin.mp equal

end SixVertexUnfolding
