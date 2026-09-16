import SixVertexUnfolding.Definitions

/-! Consecutive points of a finite real set bracket every other point
between its prescribed endpoints. -/

namespace SixVertexUnfolding

open Set

theorem finite_interval_neighbors (V : Set ℝ) (finite : V.Finite) {l r t : ℝ}
    (left : l ∈ V) (right : r ∈ V) (inside : t ∈ Icc l r) (not_vertex : t ∉ V) :
    ∃ u ∈ V, ∃ v ∈ V, u < t ∧ t < v ∧ l ≤ u ∧ v ≤ r ∧ Disjoint (Ioo u v) V := by
  let lower := V ∩ Icc l t
  let upper := V ∩ Icc t r
  have finite_lower : lower.Finite := finite.subset inter_subset_left
  have finite_upper : upper.Finite := finite.subset inter_subset_left
  obtain ⟨u, hu, greatest⟩ := finite_lower.isCompact.exists_isMaxOn
    ⟨l, left, le_rfl, inside.1⟩ continuous_id.continuousOn
  obtain ⟨v, hv, least⟩ := finite_upper.isCompact.exists_isMinOn
    ⟨r, right, inside.2, le_rfl⟩ continuous_id.continuousOn
  have ut : u < t := lt_of_le_of_ne hu.2.2 (fun same => not_vertex (same ▸ hu.1))
  have tv : t < v := lt_of_le_of_ne hv.2.1 (fun same => not_vertex (same.symm ▸ hv.1))
  refine ⟨u, hu.1, v, hv.1, ut, tv, hu.2.1, hv.2.2, disjoint_left.mpr ?_⟩
  intro x hx member
  by_cases below : x ≤ t
  · have bound : x ≤ u := greatest ⟨member, hu.2.1.trans hx.1.le, below⟩
    exact hx.1.not_ge bound
  · have bound : v ≤ x := least ⟨member, (lt_of_not_ge below).le, hx.2.le.trans hv.2.2⟩
    exact hx.2.not_ge bound

end SixVertexUnfolding
