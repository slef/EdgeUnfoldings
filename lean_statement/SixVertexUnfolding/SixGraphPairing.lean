import SixVertexUnfolding.SixGraphPairingCases

/-!
The finite six-vertex matching step. The lists contain the fifteen possible
pairings and the ten partitions into two triples (with vertex 0 in the first).
The proof is ordinary propositional reasoning checked by Lean's kernel.
-/

namespace SixVertexUnfolding.SmallGraphs

/-- The fifteen ways to pair six named vertices. -/
def pairingChoices : Fin 15 → Bool × Fin 3 → Fin 6 :=
  ![(fun v => if v.1 then ![1, 3, 5] v.2 else ![0, 2, 4] v.2),
    (fun v => if v.1 then ![1, 4, 5] v.2 else ![0, 2, 3] v.2),
    (fun v => if v.1 then ![1, 5, 4] v.2 else ![0, 2, 3] v.2),
    (fun v => if v.1 then ![2, 3, 5] v.2 else ![0, 1, 4] v.2),
    (fun v => if v.1 then ![2, 4, 5] v.2 else ![0, 1, 3] v.2),
    (fun v => if v.1 then ![2, 5, 4] v.2 else ![0, 1, 3] v.2),
    (fun v => if v.1 then ![3, 2, 5] v.2 else ![0, 1, 4] v.2),
    (fun v => if v.1 then ![3, 4, 5] v.2 else ![0, 1, 2] v.2),
    (fun v => if v.1 then ![3, 5, 4] v.2 else ![0, 1, 2] v.2),
    (fun v => if v.1 then ![4, 2, 5] v.2 else ![0, 1, 3] v.2),
    (fun v => if v.1 then ![4, 3, 5] v.2 else ![0, 1, 2] v.2),
    (fun v => if v.1 then ![4, 5, 3] v.2 else ![0, 1, 2] v.2),
    (fun v => if v.1 then ![5, 2, 4] v.2 else ![0, 1, 3] v.2),
    (fun v => if v.1 then ![5, 3, 4] v.2 else ![0, 1, 2] v.2),
    (fun v => if v.1 then ![5, 4, 3] v.2 else ![0, 1, 2] v.2)]

/-- The ten ways to split six named vertices into two triples. -/
def tripleChoices : Fin 10 → Bool × Fin 3 → Fin 6 :=
  ![(fun v => if v.1 then ![3, 4, 5] v.2 else ![0, 1, 2] v.2),
    (fun v => if v.1 then ![2, 4, 5] v.2 else ![0, 1, 3] v.2),
    (fun v => if v.1 then ![2, 3, 5] v.2 else ![0, 1, 4] v.2),
    (fun v => if v.1 then ![2, 3, 4] v.2 else ![0, 1, 5] v.2),
    (fun v => if v.1 then ![1, 4, 5] v.2 else ![0, 2, 3] v.2),
    (fun v => if v.1 then ![1, 3, 5] v.2 else ![0, 2, 4] v.2),
    (fun v => if v.1 then ![1, 3, 4] v.2 else ![0, 2, 5] v.2),
    (fun v => if v.1 then ![1, 2, 5] v.2 else ![0, 3, 4] v.2),
    (fun v => if v.1 then ![1, 2, 4] v.2 else ![0, 3, 5] v.2),
    (fun v => if v.1 then ![1, 2, 3] v.2 else ![0, 4, 5] v.2)]

theorem pairingChoices_injective : ∀ k, Function.Injective (pairingChoices k) := by decide

theorem tripleChoices_injective : ∀ k, Function.Injective (tripleChoices k) := by decide

theorem pairingChoices_bijective : ∀ k, Function.Bijective (pairingChoices k) := by decide

theorem tripleChoices_bijective : ∀ k, Function.Bijective (tripleChoices k) := by decide

set_option maxHeartbeats 3000000 in
/-- A six-vertex graph with degrees one or two either has a perfect pairing or splits into two triples. -/
theorem six_matching_or_triples (G : SimpleGraph (Fin 6))
    (nonisolated : ∀ a, ∃ b, G.Adj a b)
    (no_three : ∀ a b c d, G.Adj a b → G.Adj a c → G.Adj a d → b = c ∨ b = d ∨ c = d) :
    (∃ k : Fin 15, ∀ i : Fin 3, G.Adj (pairingChoices k (false, i)) (pairingChoices k (true, i))) ∨
    (∃ k : Fin 10, ∀ i j : Fin 3, ¬ G.Adj (tripleChoices k (false, i)) (tripleChoices k (true, j))) := by
  classical
  have bounded (a b c d : Fin 6) (bc : b ≠ c) (bd : b ≠ d) (cd : c ≠ d) :
      ¬ (G.Adj a b ∧ G.Adj a c ∧ G.Adj a d) := by
    rintro ⟨ab, ac, ad⟩
    rcases no_three a b c d ab ac ad with same | same | same
    exacts [bc same, bd same, cd same]
  have cases := six_pairing_propositional_cases (G.Adj 0 1) (G.Adj 0 2) (G.Adj 0 3) (G.Adj 0 4) (G.Adj 0 5) (G.Adj 1 2) (G.Adj 1 3) (G.Adj 1 4) (G.Adj 1 5) (G.Adj 2 3) (G.Adj 2 4) (G.Adj 2 5) (G.Adj 3 4) (G.Adj 3 5) (G.Adj 4 5)
    ⟨by
        obtain ⟨b, edge⟩ := nonisolated 0
        fin_cases b
        exacts [False.elim (edge.ne rfl), Or.inl (edge), Or.inr (Or.inl (edge)), Or.inr (Or.inr (Or.inl (edge))), Or.inr (Or.inr (Or.inr (Or.inl (edge)))), Or.inr (Or.inr (Or.inr (Or.inr (edge))))],
      by
        obtain ⟨b, edge⟩ := nonisolated 1
        fin_cases b
        exacts [Or.inl (edge.symm), False.elim (edge.ne rfl), Or.inr (Or.inl (edge)), Or.inr (Or.inr (Or.inl (edge))), Or.inr (Or.inr (Or.inr (Or.inl (edge)))), Or.inr (Or.inr (Or.inr (Or.inr (edge))))],
      by
        obtain ⟨b, edge⟩ := nonisolated 2
        fin_cases b
        exacts [Or.inl (edge.symm), Or.inr (Or.inl (edge.symm)), False.elim (edge.ne rfl), Or.inr (Or.inr (Or.inl (edge))), Or.inr (Or.inr (Or.inr (Or.inl (edge)))), Or.inr (Or.inr (Or.inr (Or.inr (edge))))],
      by
        obtain ⟨b, edge⟩ := nonisolated 3
        fin_cases b
        exacts [Or.inl (edge.symm), Or.inr (Or.inl (edge.symm)), Or.inr (Or.inr (Or.inl (edge.symm))), False.elim (edge.ne rfl), Or.inr (Or.inr (Or.inr (Or.inl (edge)))), Or.inr (Or.inr (Or.inr (Or.inr (edge))))],
      by
        obtain ⟨b, edge⟩ := nonisolated 4
        fin_cases b
        exacts [Or.inl (edge.symm), Or.inr (Or.inl (edge.symm)), Or.inr (Or.inr (Or.inl (edge.symm))), Or.inr (Or.inr (Or.inr (Or.inl (edge.symm)))), False.elim (edge.ne rfl), Or.inr (Or.inr (Or.inr (Or.inr (edge))))],
      by
        obtain ⟨b, edge⟩ := nonisolated 5
        fin_cases b
        exacts [Or.inl (edge.symm), Or.inr (Or.inl (edge.symm)), Or.inr (Or.inr (Or.inl (edge.symm))), Or.inr (Or.inr (Or.inr (Or.inl (edge.symm)))), Or.inr (Or.inr (Or.inr (Or.inr (edge.symm)))), False.elim (edge.ne rfl)]⟩
    ⟨by simpa only [SimpleGraph.adj_comm] using bounded 0 1 2 3 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using bounded 0 1 2 4 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using bounded 0 1 2 5 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using bounded 0 1 3 4 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using bounded 0 1 3 5 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using bounded 0 1 4 5 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using bounded 0 2 3 4 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using bounded 0 2 3 5 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using bounded 0 2 4 5 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using bounded 0 3 4 5 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using bounded 1 0 2 3 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using bounded 1 0 2 4 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using bounded 1 0 2 5 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using bounded 1 0 3 4 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using bounded 1 0 3 5 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using bounded 1 0 4 5 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using bounded 1 2 3 4 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using bounded 1 2 3 5 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using bounded 1 2 4 5 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using bounded 1 3 4 5 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using bounded 2 0 1 3 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using bounded 2 0 1 4 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using bounded 2 0 1 5 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using bounded 2 0 3 4 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using bounded 2 0 3 5 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using bounded 2 0 4 5 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using bounded 2 1 3 4 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using bounded 2 1 3 5 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using bounded 2 1 4 5 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using bounded 2 3 4 5 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using bounded 3 0 1 2 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using bounded 3 0 1 4 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using bounded 3 0 1 5 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using bounded 3 0 2 4 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using bounded 3 0 2 5 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using bounded 3 0 4 5 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using bounded 3 1 2 4 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using bounded 3 1 2 5 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using bounded 3 1 4 5 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using bounded 3 2 4 5 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using bounded 4 0 1 2 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using bounded 4 0 1 3 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using bounded 4 0 1 5 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using bounded 4 0 2 3 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using bounded 4 0 2 5 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using bounded 4 0 3 5 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using bounded 4 1 2 3 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using bounded 4 1 2 5 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using bounded 4 1 3 5 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using bounded 4 2 3 5 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using bounded 5 0 1 2 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using bounded 5 0 1 3 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using bounded 5 0 1 4 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using bounded 5 0 2 3 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using bounded 5 0 2 4 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using bounded 5 0 3 4 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using bounded 5 1 2 3 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using bounded 5 1 2 4 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using bounded 5 1 3 4 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using bounded 5 2 3 4 (by decide) (by decide) (by decide)⟩
  rcases cases with matching | triples
  · rcases matching with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14
    · exact Or.inl ⟨0, by simpa [Fin.forall_fin_succ, pairingChoices] using h0⟩
    · exact Or.inl ⟨1, by simpa [Fin.forall_fin_succ, pairingChoices] using h1⟩
    · exact Or.inl ⟨2, by simpa [Fin.forall_fin_succ, pairingChoices] using h2⟩
    · exact Or.inl ⟨3, by simpa [Fin.forall_fin_succ, pairingChoices] using h3⟩
    · exact Or.inl ⟨4, by simpa [Fin.forall_fin_succ, pairingChoices] using h4⟩
    · exact Or.inl ⟨5, by simpa [Fin.forall_fin_succ, pairingChoices] using h5⟩
    · exact Or.inl ⟨6, by simpa [Fin.forall_fin_succ, pairingChoices] using h6⟩
    · exact Or.inl ⟨7, by simpa [Fin.forall_fin_succ, pairingChoices] using h7⟩
    · exact Or.inl ⟨8, by simpa [Fin.forall_fin_succ, pairingChoices] using h8⟩
    · exact Or.inl ⟨9, by simpa [Fin.forall_fin_succ, pairingChoices] using h9⟩
    · exact Or.inl ⟨10, by simpa [Fin.forall_fin_succ, pairingChoices] using h10⟩
    · exact Or.inl ⟨11, by simpa [Fin.forall_fin_succ, pairingChoices] using h11⟩
    · exact Or.inl ⟨12, by simpa [Fin.forall_fin_succ, pairingChoices] using h12⟩
    · exact Or.inl ⟨13, by simpa [Fin.forall_fin_succ, pairingChoices] using h13⟩
    · exact Or.inl ⟨14, by simpa [Fin.forall_fin_succ, pairingChoices] using h14⟩
  · rcases triples with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
    · exact Or.inr ⟨0, by simpa [Fin.forall_fin_succ, tripleChoices, SimpleGraph.adj_comm, and_assoc] using h0⟩
    · exact Or.inr ⟨1, by simpa [Fin.forall_fin_succ, tripleChoices, SimpleGraph.adj_comm, and_assoc] using h1⟩
    · exact Or.inr ⟨2, by simpa [Fin.forall_fin_succ, tripleChoices, SimpleGraph.adj_comm, and_assoc] using h2⟩
    · exact Or.inr ⟨3, by simpa [Fin.forall_fin_succ, tripleChoices, SimpleGraph.adj_comm, and_assoc] using h3⟩
    · exact Or.inr ⟨4, by simpa [Fin.forall_fin_succ, tripleChoices, SimpleGraph.adj_comm, and_assoc] using h4⟩
    · exact Or.inr ⟨5, by simpa [Fin.forall_fin_succ, tripleChoices, SimpleGraph.adj_comm, and_assoc] using h5⟩
    · exact Or.inr ⟨6, by simpa [Fin.forall_fin_succ, tripleChoices, SimpleGraph.adj_comm, and_assoc] using h6⟩
    · exact Or.inr ⟨7, by simpa [Fin.forall_fin_succ, tripleChoices, SimpleGraph.adj_comm, and_assoc] using h7⟩
    · exact Or.inr ⟨8, by simpa [Fin.forall_fin_succ, tripleChoices, SimpleGraph.adj_comm, and_assoc] using h8⟩
    · exact Or.inr ⟨9, by simpa [Fin.forall_fin_succ, tripleChoices, SimpleGraph.adj_comm, and_assoc] using h9⟩

end SixVertexUnfolding.SmallGraphs
