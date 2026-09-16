import SixVertexUnfolding.Geometry.ThreeByThreeExclusion
import SixVertexUnfolding.Geometry.SmallPolyhedra
import SixVertexUnfolding.SixGraphPairing

/-! Three opposite pairs of original vertices in the six-vertex case without a universal vertex. -/

namespace SixVertexUnfolding.SmallGraphs

/-- A vertex of degree at most two cannot have three distinct neighbors. -/
theorem no_three_neighbors {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b c d : V) (bound : Nat.card (G.neighborSet a) ≤ 2)
    (ab : G.Adj a b) (ac : G.Adj a c) (ad : G.Adj a d) : b = c ∨ b = d ∨ c = d := by
  classical
  by_contra different
  push Not at different
  have subset : ({b, c, d} : Finset V) ⊆ G.neighborFinset a := by
    intro x member
    rcases Finset.mem_insert.mp member with rfl | member
    · exact G.mem_neighborFinset a _ |>.mpr ab
    rcases Finset.mem_insert.mp member with rfl | member
    · exact G.mem_neighborFinset a _ |>.mpr ac
    have equal : x = d := Finset.mem_singleton.mp member
    subst x
    exact G.mem_neighborFinset a d |>.mpr ad
  have lower := Finset.card_le_card subset
  have three : ({b, c, d} : Finset V).card = 3 := by simp [different.1, different.2.1, different.2.2]
  rw [three, G.card_neighborFinset_eq_degree] at lower
  have upper : G.degree a ≤ 2 := by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using bound
  omega

end SixVertexUnfolding.SmallGraphs

namespace SixVertexUnfolding.ConvexPolyhedron

/-- Six original vertices labeled as three disjoint pairs of nonneighbors. -/
structure OppositePairs (P : ConvexPolyhedron) where
  vertex : (Bool × Fin 3) ≃ P.Vertex
  nonedge : ∀ i : Fin 3, ¬ P.edgeGraph.Adj (vertex (false, i)) (vertex (true, i))

/-- Without a universal vertex, a six-vertex solid has at most two nonneighbors at each vertex. -/
theorem six_vertices_no_three_nonneighbors (P : ConvexPolyhedron) (size : P.vertices.card = 6)
    (no_universal : ¬ ∃ v : P.Vertex, ∀ w, w ≠ v → P.edgeGraph.Adj v w)
    (a b c d : P.Vertex) (ab : P.edgeGraphᶜ.Adj a b) (ac : P.edgeGraphᶜ.Adj a c)
    (ad : P.edgeGraphᶜ.Adj a d) : b = c ∨ b = d ∨ c = d := by
  classical
  have degree := P.six_vertices_complement_degrees size no_universal a
  have bound : Nat.card (P.edgeGraphᶜ.neighborSet a) ≤ 2 := by
    have degree' : Nat.card (P.edgeGraphᶜ.neighborSet a) = 1 ∨
        Nat.card (P.edgeGraphᶜ.neighborSet a) = 2 := by
      simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using degree
    omega
  exact SmallGraphs.no_three_neighbors P.edgeGraphᶜ a b c d bound ab ac ad

/-- The remaining six-vertex surface admits three pairs of nonadjacent original vertices. -/
theorem exists_opposite_pairs (P : ConvexPolyhedron) (size : P.vertices.card = 6)
    (no_universal : ¬ ∃ v : P.Vertex, ∀ w, w ≠ v → P.edgeGraph.Adj v w)
    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4) : Nonempty P.OppositePairs := by
  classical
  let index : Fin 6 ≃ P.Vertex := (Fintype.equivFinOfCardEq (P.vertex_card.trans size)).symm
  let graph := P.edgeGraphᶜ.comap index
  have nonisolated (a : Fin 6) : ∃ b, graph.Adj a b := by
    have other : ∃ w : P.Vertex, w ≠ index a ∧ ¬ P.edgeGraph.Adj (index a) w := by
      by_contra all_adjacent
      push Not at all_adjacent
      exact no_universal ⟨index a, all_adjacent⟩
    obtain ⟨w, different, not_edge⟩ := other
    refine ⟨index.symm w, ?_⟩
    change P.edgeGraphᶜ.Adj (index a) (index (index.symm w))
    rw [index.apply_symm_apply, SimpleGraph.compl_adj]
    exact ⟨different.symm, not_edge⟩
  have no_three (a b c d : Fin 6) (ab : graph.Adj a b) (ac : graph.Adj a c) (ad : graph.Adj a d) :
      b = c ∨ b = d ∨ c = d := by
    rcases P.six_vertices_no_three_nonneighbors size no_universal (index a) (index b) (index c) (index d)
        ab ac ad with same | same | same
    exacts [Or.inl (index.injective same), Or.inr (Or.inl (index.injective same)),
      Or.inr (Or.inr (index.injective same))]
  rcases SmallGraphs.six_matching_or_triples graph nonisolated no_three with matching | split
  · obtain ⟨k, pairs⟩ := matching
    let labels : (Bool × Fin 3) ≃ Fin 6 := Equiv.ofBijective (SmallGraphs.pairingChoices k)
      (SmallGraphs.pairingChoices_bijective k)
    refine ⟨⟨labels.trans index, ?_⟩⟩
    intro i
    exact (pairs i).2
  · obtain ⟨k, separated⟩ := split
    let labels : (Bool × Fin 3) ≃ Fin 6 := Equiv.ofBijective (SmallGraphs.tripleChoices k)
      (SmallGraphs.tripleChoices_bijective k)
    let triple : P.ThreeByThree := {
      vertex := labels.trans index
      across := by
        intro i j
        by_contra missing
        apply separated i j
        change index (labels (false, i)) ≠ index (labels (true, j)) ∧
          ¬ P.edgeGraph.Adj (index (labels (false, i))) (index (labels (true, j)))
        refine ⟨?_, missing⟩
        intro same
        have impossible := congrArg Prod.fst (labels.injective (index.injective same))
        cases impossible
    }
    exact False.elim (triple.impossible no_universal small_faces)

end SixVertexUnfolding.ConvexPolyhedron
