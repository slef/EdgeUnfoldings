import SixVertexUnfolding.Definitions

/-! Turn a spanning simple cycle on five vertices into a concrete cyclic
numbering. This is only a graph lemma; its later application uses actual faces. -/

namespace SixVertexUnfolding

/-- A spanning simple cycle orders the five vertices with consecutive vertices adjacent. -/
theorem five_cycle_order {V : Type*} [Fintype V] (G : SimpleGraph V)
    (five : Fintype.card V = 5) {b : V} (p : G.Walk b b) (cycle : p.IsCycle)
    (covers : p.toSubgraph.verts = Set.univ) :
    ∃ order : Fin 5 ≃ V, ∀ i : Fin 5, G.Adj (order i) (order (i + 1)) := by
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
  have length : p.length = 5 := by
    have same_card := Fintype.card_congr (Equiv.ofBijective visit ⟨injective, surjective⟩)
    simpa only [Fintype.card_fin, five] using same_card
  let order : Fin 5 ≃ V := (finCongr length).symm.trans (Equiv.ofBijective visit ⟨injective, surjective⟩)
  have order_eq (i : Fin 5) : order i = p.getVert i := rfl
  refine ⟨order, ?_⟩
  intro i
  rw [order_eq, order_eq]
  have next := p.adj_getVert_succ (i := i.val) (by omega)
  have closes : p.getVert 5 = p.getVert 0 := by rw [← length, p.getVert_length, p.getVert_zero]
  fin_cases i <;> simpa only [Fin.val_add, Fin.val_one, Fin.val_zero, Fin.val_ofNat,
    Nat.reduceAdd, Nat.reduceMod, closes] using next

/-- The predecessor and successor exhaust the neighbors in a two-regular five-cycle. -/
theorem five_cycle_neighbors {V : Type*} [Finite V] (G : SimpleGraph V)
    (two : ∀ v, (G.neighborSet v).ncard = 2) (order : Fin 5 ≃ V)
    (consecutive : ∀ i : Fin 5, G.Adj (order i) (order (i + 1))) (i : Fin 5) :
    G.neighborSet (order i) = {order (i - 1), order (i + 1)} := by
  have different : order (i - 1) ≠ order (i + 1) := by
    intro same
    have impossible := order.injective same
    exact (by decide : ∀ i : Fin 5, i - 1 ≠ i + 1) i impossible
  have contained : ({order (i - 1), order (i + 1)} : Set V) ⊆ G.neighborSet (order i) := by
    rintro x (rfl | rfl)
    · simpa only [sub_add_cancel] using (consecutive (i - 1)).symm
    · exact consecutive i
  exact (Set.eq_of_subset_of_ncard_le contained (by rw [two, Set.ncard_pair different])).symm

end SixVertexUnfolding
