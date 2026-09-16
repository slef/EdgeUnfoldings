import SixVertexUnfolding.CanonicalSixGraphs

/-! Classify an original six-vertex complement once a perfect pairing is fixed. -/

namespace SixVertexUnfolding.SmallGraphs

/-- The partner in the fixed pairs 01, 23, and 45. -/
def fixedPartner : Fin 6 → Fin 6 := ![1, 0, 3, 2, 5, 4]

set_option maxHeartbeats 6000000 in
/-- Degrees at most two and the four-cycle exclusion leave precisely four graph forms. -/
theorem classify_paired_graph (G : SimpleGraph (Fin 6))
    (base01 : G.Adj 0 1) (base23 : G.Adj 2 3) (base45 : G.Adj 4 5)
    (no_three : ∀ a b c d, G.Adj a b → G.Adj a c → G.Adj a d → b = c ∨ b = d ∨ c = d)
    (no_square : ∀ labels : Fin 6 ≃ Fin 6,
      ¬ (G.Adj (labels 0) (labels 2) ∧ G.Adj (labels 0) (labels 3) ∧
        G.Adj (labels 1) (labels 2) ∧ G.Adj (labels 1) (labels 3))) :
    ∃ k : Fin 45, ∀ i j : Fin 6,
      G.Adj ((pairedGraphChoices k).2 i) ((pairedGraphChoices k).2 j) ↔
        s(i, j) ∈ (pairedGraphChoices k).1.missingEdges := by
  classical
  have partner_edges (a : Fin 6) : G.Adj a (fixedPartner a) := by
    fin_cases a
    exacts [base01, base01.symm, base23, base23.symm, base45, base45.symm]
  have no_two_extra (a b c : Fin 6) (bc : b ≠ c) (bp : b ≠ fixedPartner a) (cp : c ≠ fixedPartner a) :
      ¬ (G.Adj a b ∧ G.Adj a c) := by
    rintro ⟨ab, ac⟩
    rcases no_three a b c (fixedPartner a) ab ac (partner_edges a) with same | same | same
    exacts [bc same, bp same, cp same]
  have cases := paired_graph_propositional_cases (G.Adj 0 2) (G.Adj 0 3) (G.Adj 0 4) (G.Adj 0 5) (G.Adj 1 2) (G.Adj 1 3) (G.Adj 1 4) (G.Adj 1 5) (G.Adj 2 4) (G.Adj 2 5) (G.Adj 3 4) (G.Adj 3 5)
    ⟨by simpa only [SimpleGraph.adj_comm] using no_two_extra 0 2 3 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using no_two_extra 0 2 4 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using no_two_extra 0 2 5 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using no_two_extra 2 0 1 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using no_two_extra 2 0 4 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using no_two_extra 2 0 5 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using no_two_extra 0 3 4 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using no_two_extra 0 3 5 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using no_two_extra 3 0 1 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using no_two_extra 3 0 4 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using no_two_extra 3 0 5 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using no_two_extra 0 4 5 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using no_two_extra 4 0 1 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using no_two_extra 4 0 2 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using no_two_extra 4 0 3 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using no_two_extra 5 0 1 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using no_two_extra 5 0 2 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using no_two_extra 5 0 3 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using no_two_extra 1 2 3 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using no_two_extra 1 2 4 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using no_two_extra 1 2 5 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using no_two_extra 2 1 4 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using no_two_extra 2 1 5 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using no_two_extra 1 3 4 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using no_two_extra 1 3 5 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using no_two_extra 3 1 4 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using no_two_extra 3 1 5 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using no_two_extra 1 4 5 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using no_two_extra 4 1 2 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using no_two_extra 4 1 3 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using no_two_extra 5 1 2 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using no_two_extra 5 1 3 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using no_two_extra 2 4 5 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using no_two_extra 4 2 3 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using no_two_extra 5 2 3 (by decide) (by decide) (by decide),
      by simpa only [SimpleGraph.adj_comm] using no_two_extra 3 4 5 (by decide) (by decide) (by decide)⟩
    ⟨by
        rintro ⟨first, second⟩
        let labels : Fin 6 ≃ Fin 6 := Equiv.ofBijective ![0, 3, 1, 2, 4, 5] (by decide)
        exact no_square labels ⟨base01, first, second.symm, base23.symm⟩,
      by
        rintro ⟨first, second⟩
        let labels : Fin 6 ≃ Fin 6 := Equiv.ofBijective ![0, 2, 1, 3, 4, 5] (by decide)
        exact no_square labels ⟨base01, first, second.symm, base23⟩,
      by
        rintro ⟨first, second⟩
        let labels : Fin 6 ≃ Fin 6 := Equiv.ofBijective ![0, 5, 1, 4, 2, 3] (by decide)
        exact no_square labels ⟨base01, first, second.symm, base45.symm⟩,
      by
        rintro ⟨first, second⟩
        let labels : Fin 6 ≃ Fin 6 := Equiv.ofBijective ![0, 4, 1, 5, 2, 3] (by decide)
        exact no_square labels ⟨base01, first, second.symm, base45⟩,
      by
        rintro ⟨first, second⟩
        let labels : Fin 6 ≃ Fin 6 := Equiv.ofBijective ![2, 5, 3, 4, 0, 1] (by decide)
        exact no_square labels ⟨base23, first, second.symm, base45.symm⟩,
      by
        rintro ⟨first, second⟩
        let labels : Fin 6 ≃ Fin 6 := Equiv.ofBijective ![2, 4, 3, 5, 0, 1] (by decide)
        exact no_square labels ⟨base23, first, second.symm, base45⟩⟩
  clear no_two_extra partner_edges no_three no_square
  rcases cases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39 | h40 | h41 | h42 | h43 | h44
  · refine ⟨0, ?_⟩
    simp only [Fin.forall_fin_succ]
    simp_all [pairedGraphChoices, SixGraphKind.missingEdges, SimpleGraph.adj_comm]
  · refine ⟨1, ?_⟩
    simp only [Fin.forall_fin_succ]
    simp_all [pairedGraphChoices, SixGraphKind.missingEdges, SimpleGraph.adj_comm]
  · refine ⟨2, ?_⟩
    simp only [Fin.forall_fin_succ]
    simp_all [pairedGraphChoices, SixGraphKind.missingEdges, SimpleGraph.adj_comm]
  · refine ⟨3, ?_⟩
    simp only [Fin.forall_fin_succ]
    simp_all [pairedGraphChoices, SixGraphKind.missingEdges, SimpleGraph.adj_comm]
  · refine ⟨4, ?_⟩
    simp only [Fin.forall_fin_succ]
    simp_all [pairedGraphChoices, SixGraphKind.missingEdges, SimpleGraph.adj_comm]
  · refine ⟨5, ?_⟩
    simp only [Fin.forall_fin_succ]
    simp_all [pairedGraphChoices, SixGraphKind.missingEdges, SimpleGraph.adj_comm]
  · refine ⟨6, ?_⟩
    simp only [Fin.forall_fin_succ]
    simp_all [pairedGraphChoices, SixGraphKind.missingEdges, SimpleGraph.adj_comm]
  · refine ⟨7, ?_⟩
    simp only [Fin.forall_fin_succ]
    simp_all [pairedGraphChoices, SixGraphKind.missingEdges, SimpleGraph.adj_comm]
  · refine ⟨8, ?_⟩
    simp only [Fin.forall_fin_succ]
    simp_all [pairedGraphChoices, SixGraphKind.missingEdges, SimpleGraph.adj_comm]
  · refine ⟨9, ?_⟩
    simp only [Fin.forall_fin_succ]
    simp_all [pairedGraphChoices, SixGraphKind.missingEdges, SimpleGraph.adj_comm]
  · refine ⟨10, ?_⟩
    simp only [Fin.forall_fin_succ]
    simp_all [pairedGraphChoices, SixGraphKind.missingEdges, SimpleGraph.adj_comm]
  · refine ⟨11, ?_⟩
    simp only [Fin.forall_fin_succ]
    simp_all [pairedGraphChoices, SixGraphKind.missingEdges, SimpleGraph.adj_comm]
  · refine ⟨12, ?_⟩
    simp only [Fin.forall_fin_succ]
    simp_all [pairedGraphChoices, SixGraphKind.missingEdges, SimpleGraph.adj_comm]
  · refine ⟨13, ?_⟩
    simp only [Fin.forall_fin_succ]
    simp_all [pairedGraphChoices, SixGraphKind.missingEdges, SimpleGraph.adj_comm]
  · refine ⟨14, ?_⟩
    simp only [Fin.forall_fin_succ]
    simp_all [pairedGraphChoices, SixGraphKind.missingEdges, SimpleGraph.adj_comm]
  · refine ⟨15, ?_⟩
    simp only [Fin.forall_fin_succ]
    simp_all [pairedGraphChoices, SixGraphKind.missingEdges, SimpleGraph.adj_comm]
  · refine ⟨16, ?_⟩
    simp only [Fin.forall_fin_succ]
    simp_all [pairedGraphChoices, SixGraphKind.missingEdges, SimpleGraph.adj_comm]
  · refine ⟨17, ?_⟩
    simp only [Fin.forall_fin_succ]
    simp_all [pairedGraphChoices, SixGraphKind.missingEdges, SimpleGraph.adj_comm]
  · refine ⟨18, ?_⟩
    simp only [Fin.forall_fin_succ]
    simp_all [pairedGraphChoices, SixGraphKind.missingEdges, SimpleGraph.adj_comm]
  · refine ⟨19, ?_⟩
    simp only [Fin.forall_fin_succ]
    simp_all [pairedGraphChoices, SixGraphKind.missingEdges, SimpleGraph.adj_comm]
  · refine ⟨20, ?_⟩
    simp only [Fin.forall_fin_succ]
    simp_all [pairedGraphChoices, SixGraphKind.missingEdges, SimpleGraph.adj_comm]
  · refine ⟨21, ?_⟩
    simp only [Fin.forall_fin_succ]
    simp_all [pairedGraphChoices, SixGraphKind.missingEdges, SimpleGraph.adj_comm]
  · refine ⟨22, ?_⟩
    simp only [Fin.forall_fin_succ]
    simp_all [pairedGraphChoices, SixGraphKind.missingEdges, SimpleGraph.adj_comm]
  · refine ⟨23, ?_⟩
    simp only [Fin.forall_fin_succ]
    simp_all [pairedGraphChoices, SixGraphKind.missingEdges, SimpleGraph.adj_comm]
  · refine ⟨24, ?_⟩
    simp only [Fin.forall_fin_succ]
    simp_all [pairedGraphChoices, SixGraphKind.missingEdges, SimpleGraph.adj_comm]
  · refine ⟨25, ?_⟩
    simp only [Fin.forall_fin_succ]
    simp_all [pairedGraphChoices, SixGraphKind.missingEdges, SimpleGraph.adj_comm]
  · refine ⟨26, ?_⟩
    simp only [Fin.forall_fin_succ]
    simp_all [pairedGraphChoices, SixGraphKind.missingEdges, SimpleGraph.adj_comm]
  · refine ⟨27, ?_⟩
    simp only [Fin.forall_fin_succ]
    simp_all [pairedGraphChoices, SixGraphKind.missingEdges, SimpleGraph.adj_comm]
  · refine ⟨28, ?_⟩
    simp only [Fin.forall_fin_succ]
    simp_all [pairedGraphChoices, SixGraphKind.missingEdges, SimpleGraph.adj_comm]
  · refine ⟨29, ?_⟩
    simp only [Fin.forall_fin_succ]
    simp_all [pairedGraphChoices, SixGraphKind.missingEdges, SimpleGraph.adj_comm]
  · refine ⟨30, ?_⟩
    simp only [Fin.forall_fin_succ]
    simp_all [pairedGraphChoices, SixGraphKind.missingEdges, SimpleGraph.adj_comm]
  · refine ⟨31, ?_⟩
    simp only [Fin.forall_fin_succ]
    simp_all [pairedGraphChoices, SixGraphKind.missingEdges, SimpleGraph.adj_comm]
  · refine ⟨32, ?_⟩
    simp only [Fin.forall_fin_succ]
    simp_all [pairedGraphChoices, SixGraphKind.missingEdges, SimpleGraph.adj_comm]
  · refine ⟨33, ?_⟩
    simp only [Fin.forall_fin_succ]
    simp_all [pairedGraphChoices, SixGraphKind.missingEdges, SimpleGraph.adj_comm]
  · refine ⟨34, ?_⟩
    simp only [Fin.forall_fin_succ]
    simp_all [pairedGraphChoices, SixGraphKind.missingEdges, SimpleGraph.adj_comm]
  · refine ⟨35, ?_⟩
    simp only [Fin.forall_fin_succ]
    simp_all [pairedGraphChoices, SixGraphKind.missingEdges, SimpleGraph.adj_comm]
  · refine ⟨36, ?_⟩
    simp only [Fin.forall_fin_succ]
    simp_all [pairedGraphChoices, SixGraphKind.missingEdges, SimpleGraph.adj_comm]
  · refine ⟨37, ?_⟩
    simp only [Fin.forall_fin_succ]
    simp_all [pairedGraphChoices, SixGraphKind.missingEdges, SimpleGraph.adj_comm]
  · refine ⟨38, ?_⟩
    simp only [Fin.forall_fin_succ]
    simp_all [pairedGraphChoices, SixGraphKind.missingEdges, SimpleGraph.adj_comm]
  · refine ⟨39, ?_⟩
    simp only [Fin.forall_fin_succ]
    simp_all [pairedGraphChoices, SixGraphKind.missingEdges, SimpleGraph.adj_comm]
  · refine ⟨40, ?_⟩
    simp only [Fin.forall_fin_succ]
    simp_all [pairedGraphChoices, SixGraphKind.missingEdges, SimpleGraph.adj_comm]
  · refine ⟨41, ?_⟩
    simp only [Fin.forall_fin_succ]
    simp_all [pairedGraphChoices, SixGraphKind.missingEdges, SimpleGraph.adj_comm]
  · refine ⟨42, ?_⟩
    simp only [Fin.forall_fin_succ]
    simp_all [pairedGraphChoices, SixGraphKind.missingEdges, SimpleGraph.adj_comm]
  · refine ⟨43, ?_⟩
    simp only [Fin.forall_fin_succ]
    simp_all [pairedGraphChoices, SixGraphKind.missingEdges, SimpleGraph.adj_comm]
  · refine ⟨44, ?_⟩
    simp only [Fin.forall_fin_succ]
    simp_all [pairedGraphChoices, SixGraphKind.missingEdges, SimpleGraph.adj_comm]

end SixVertexUnfolding.SmallGraphs
