import SixVertexUnfolding.Definitions

/-! Turn a spanning simple cycle into a cyclic numbering of its vertices. -/

namespace SixVertexUnfolding

/-- A spanning simple cycle orders all vertices, with consecutive vertices adjacent. -/
theorem spanning_cycle_order {V : Type*} [Fintype V] (G : SimpleGraph V)
    {n : ℕ} [NeZero n] (count : Fintype.card V = n) {b : V} (p : G.Walk b b) (cycle : p.IsCycle)
    (covers : p.toSubgraph.verts = Set.univ) :
    ∃ order : Fin n ≃ V, ∀ i : Fin n, G.Adj (order i) (order (i + 1)) := by
  classical
  let visit : Fin p.length → V := fun i => p.getVert i
  have injective : Function.Injective visit := by
    intro i j same
    apply Fin.ext
    exact cycle.getVert_injOn' (by change i.val ≤ p.length - 1; omega)
      (by change j.val ≤ p.length - 1; omega) same
  have surjective : Function.Surjective visit := by
    intro v
    have member : v ∈ p.support := p.mem_verts_toSubgraph.mp (covers.symm ▸ Set.mem_univ v)
    obtain ⟨i, at_v, before⟩ := p.mem_support_iff_exists_getVert.mp member
    by_cases last : i = p.length
    · refine ⟨⟨0, by have := cycle.three_le_length; omega⟩, ?_⟩
      change p.getVert 0 = v
      rw [last, p.getVert_length] at at_v
      simpa only [p.getVert_zero] using at_v
    · exact ⟨⟨i, lt_of_le_of_ne before last⟩, at_v⟩
  have length : p.length = n := by
    have same_card := Fintype.card_congr (Equiv.ofBijective visit ⟨injective, surjective⟩)
    simpa only [Fintype.card_fin, count] using same_card
  let order : Fin n ≃ V := (finCongr length).symm.trans (Equiv.ofBijective visit ⟨injective, surjective⟩)
  have order_eq (i : Fin n) : order i = p.getVert i := rfl
  refine ⟨order, ?_⟩
  intro i
  rw [order_eq, order_eq]
  have next := p.adj_getVert_succ (i := i.val) (by omega)
  have one_lt : 1 < n := by have := cycle.three_le_length; omega
  have next_val : (i + 1).val = (i.val + 1) % n := by
    change (i.val + 1 % n) % n = _
    rw [Nat.mod_eq_of_lt one_lt]
  rw [next_val]
  by_cases last : i.val + 1 = n
  · rw [last, Nat.mod_self]
    have closes : p.getVert (i.val + 1) = p.getVert 0 := by
      rw [last, ← length, p.getVert_length, p.getVert_zero]
    rwa [closes] at next
  · rw [Nat.mod_eq_of_lt (show i.val + 1 < n by omega)]
    exact next

/-- In a two-regular cycle, only the predecessor and successor are adjacent. -/
theorem spanning_cycle_neighbors {V : Type*} [Finite V] (G : SimpleGraph V)
    {n : ℕ} [NeZero n] (three : 3 ≤ n)
    (two : ∀ v, (G.neighborSet v).ncard = 2) (order : Fin n ≃ V)
    (consecutive : ∀ i : Fin n, G.Adj (order i) (order (i + 1))) (i : Fin n) :
    G.neighborSet (order i) = {order (i - 1), order (i + 1)} := by
  have different : order (i - 1) ≠ order (i + 1) := by
    intro same
    have impossible := congrArg (fun j : Fin n => j + 1) (order.injective same)
    dsimp at impossible
    rw [sub_add_cancel, add_assoc] at impossible
    have zero : (0 : Fin n) = 1 + 1 := add_left_cancel
      (show i + 0 = i + (1 + 1) by simpa only [add_zero] using impossible)
    have values := congrArg Fin.val zero
    change 0 = (1 % n + 1 % n) % n at values
    simp only [Nat.mod_eq_of_lt (show 1 < n by omega),
      show 1 + 1 = 2 from rfl, Nat.mod_eq_of_lt (show 2 < n by omega)] at values
    omega
  have contained : ({order (i - 1), order (i + 1)} : Set V) ⊆ G.neighborSet (order i) := by
    rintro x (rfl | rfl)
    · simpa only [sub_add_cancel] using (consecutive (i - 1)).symm
    · exact consecutive i
  exact (Set.eq_of_subset_of_ncard_le contained (by rw [two, Set.ncard_pair different])).symm

end SixVertexUnfolding
