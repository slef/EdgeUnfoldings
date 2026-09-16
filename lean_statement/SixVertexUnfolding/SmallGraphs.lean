import Mathlib

/-!
The elementary graph part of the first classification step in TIDY_PROOF.md.
Geometry/SmallPolyhedra applies these results to the original vertex-edge graph.
-/

namespace SixVertexUnfolding.SmallGraphs

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem adjacent_to_all_of_max_degree
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (max_degree : G.degree v = Fintype.card V - 1) :
    ∀ w, w ≠ v → G.Adj v w := by
  classical
  have subset : G.neighborFinset v ⊆ Finset.univ.erase v := by
    intro w hw
    have adjacent : G.Adj v w := (G.mem_neighborFinset v w).mp hw
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact adjacent.ne.symm
  have same : G.neighborFinset v = Finset.univ.erase v :=
    Finset.eq_of_subset_of_card_le subset (by simp [max_degree])
  intro w distinct
  apply (G.mem_neighborFinset v w).mp
  rw [same]
  simp [distinct]

/-- The four-vertex case has a vertex adjacent to all others. -/
theorem four_vertices_have_universal_vertex
    (G : SimpleGraph V) [DecidableRel G.Adj] (size : Fintype.card V = 4)
    (minimum_degree : ∀ v, 3 ≤ G.degree v) :
    ∃ v, ∀ w, w ≠ v → G.Adj v w := by
  obtain ⟨v⟩ := Fintype.card_pos_iff.mp (show 0 < Fintype.card V by omega)
  refine ⟨v, adjacent_to_all_of_max_degree G v ?_⟩
  have lower := minimum_degree v
  have upper := G.degree_lt_card_verts v
  omega

omit [DecidableEq V] in
/-- Five vertices cannot all have degree three: the sum of degrees is even. -/
theorem five_vertices_have_degree_four
    (G : SimpleGraph V) [DecidableRel G.Adj] (size : Fintype.card V = 5)
    (minimum_degree : ∀ v, 3 ≤ G.degree v) : ∃ v, G.degree v = 4 := by
  classical
  by_contra no_four
  push Not at no_four
  have all_three (v : V) : G.degree v = 3 := by
    have lower := minimum_degree v
    have upper := G.degree_lt_card_verts v
    have not_four := no_four v
    omega
  have handshake := G.sum_degrees_eq_twice_card_edges
  simp only [all_three, Finset.sum_const, Finset.card_univ, size,
    smul_eq_mul] at handshake
  omega

theorem five_vertices_have_universal_vertex
    (G : SimpleGraph V) [DecidableRel G.Adj] (size : Fintype.card V = 5)
    (minimum_degree : ∀ v, 3 ≤ G.degree v) :
    ∃ v, ∀ w, w ≠ v → G.Adj v w := by
  obtain ⟨v, degree_four⟩ := five_vertices_have_degree_four G size minimum_degree
  exact ⟨v, adjacent_to_all_of_max_degree G v (by omega)⟩

/-- Without a degree-five vertex, the six-vertex complement has degrees one or two. -/
theorem six_vertex_complement_degrees
    (G : SimpleGraph V) [DecidableRel G.Adj] (size : Fintype.card V = 6)
    (minimum_degree : ∀ v, 3 ≤ G.degree v)
    (no_degree_five : ∀ v, G.degree v ≠ 5) (v : V) :
    Gᶜ.degree v = 1 ∨ Gᶜ.degree v = 2 := by
  have lower := minimum_degree v
  have upper := G.degree_lt_card_verts v
  have not_five := no_degree_five v
  have complement := G.degree_compl v
  omega

end SixVertexUnfolding.SmallGraphs
