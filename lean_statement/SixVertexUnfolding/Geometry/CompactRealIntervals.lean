import SixVertexUnfolding.Definitions

/-! A compact subset of the real line with finitely many boundary points
is exactly a finite union of closed intervals, allowing singletons. -/

namespace SixVertexUnfolding

open Set

theorem compact_real_component (K : Set ℝ) (compact : IsCompact K) {x : ℝ} (hx : x ∈ K) :
    IsCompact (connectedComponentIn K x) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp compact
  rw [connectedComponentIn_eq_image hx]
  exact isClosed_connectedComponent.isCompact.image continuous_subtype_val

/-- A component of a compact real set acquires no new boundary points inside that set's interior. -/
theorem frontier_real_component_subset (K : Set ℝ) (compact : IsCompact K) {x : ℝ} (hx : x ∈ K) :
    frontier (connectedComponentIn K x) ⊆ frontier K := by
  intro y hy
  rw [frontier, (compact_real_component K compact hx).isClosed.closure_eq] at hy
  refine ⟨subset_closure (connectedComponentIn_subset K x hy.1), ?_⟩
  intro inside
  obtain ⟨δ, positive, disk⟩ := Metric.isOpen_iff.mp isOpen_interior y inside
  have in_component : Metric.ball y δ ⊆ connectedComponentIn K x := by
    rw [connectedComponentIn_eq hy.1]
    exact (convex_ball y δ).isPreconnected.subset_connectedComponentIn
      (Metric.mem_ball_self positive) (disk.trans interior_subset)
  apply hy.2
  exact mem_interior_iff_mem_nhds.mpr
    (Filter.mem_of_superset (Metric.ball_mem_nhds y positive) in_component)

/-- Every point lies in a whole closed interval in the set, whose endpoints are boundary points. -/
theorem compact_real_interval_through (K : Set ℝ) (compact : IsCompact K) {x : ℝ} (hx : x ∈ K) :
    ∃ l ∈ frontier K, ∃ r ∈ frontier K, x ∈ Icc l r ∧ Icc l r ⊆ K := by
  let C := connectedComponentIn K x
  have compactC : IsCompact C := compact_real_component K compact hx
  have connectedC : IsConnected C := isConnected_connectedComponentIn_iff.mpr hx
  obtain ⟨l, hl, least⟩ := compactC.exists_isMinOn connectedC.nonempty continuous_id.continuousOn
  obtain ⟨r, hr, greatest⟩ := compactC.exists_isMaxOn connectedC.nonempty continuous_id.continuousOn
  have interval : C = Icc l r := by
    apply Subset.antisymm
    · exact fun y hy => ⟨least hy, greatest hy⟩
    · exact connectedC.isPreconnected.ordConnected.out hl hr
  have ordered : l ≤ r := least hr
  have left_boundary : l ∈ frontier C := by
    rw [interval, frontier_Icc ordered]
    simp
  have right_boundary : r ∈ frontier C := by
    rw [interval, frontier_Icc ordered]
    simp
  refine ⟨l, frontier_real_component_subset K compact hx left_boundary,
    r, frontier_real_component_subset K compact hx right_boundary, ?_, ?_⟩
  · rw [← interval]
    exact mem_connectedComponentIn hx
  · rw [← interval]
    exact connectedComponentIn_subset K x

/-- Finitely many boundary parameters give an exact finite union of closed intervals. -/
theorem compact_real_finite_intervals (K : Set ℝ) (compact : IsCompact K)
    (finite_boundary : (frontier K).Finite) :
    ∃ pieces : Set (ℝ × ℝ), pieces.Finite ∧
      (∀ p ∈ pieces, p.1 ≤ p.2 ∧ Icc p.1 p.2 ⊆ K) ∧ K = ⋃ p ∈ pieces, Icc p.1 p.2 := by
  let pieces := {p : ℝ × ℝ | p.1 ∈ frontier K ∧ p.2 ∈ frontier K ∧
    p.1 ≤ p.2 ∧ Icc p.1 p.2 ⊆ K}
  refine ⟨pieces, (finite_boundary.prod finite_boundary).subset (fun _ h => ⟨h.1, h.2.1⟩),
    fun _ h => h.2.2, ?_⟩
  apply Subset.antisymm
  · intro x hx
    obtain ⟨l, hl, r, hr, inside, contained⟩ := compact_real_interval_through K compact hx
    exact mem_iUnion.mpr ⟨(l, r), mem_iUnion.mpr ⟨⟨hl, hr, inside.1.trans inside.2, contained⟩, inside⟩⟩
  · intro x hx
    obtain ⟨p, inside⟩ := mem_iUnion.mp hx
    obtain ⟨member, inside⟩ := mem_iUnion.mp inside
    exact member.2.2.2 inside

end SixVertexUnfolding
