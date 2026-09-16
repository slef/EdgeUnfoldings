import SixVertexUnfolding.Geometry.FiveVertexNonedge

/-! The five-vertex graph is complete except for one or two disjoint missing edges. -/

namespace SixVertexUnfolding.ConvexPolyhedron

/-- At five vertices, no vertex has more than one nonneighbor. -/
theorem five_vertices_complement_degree_le_one (P : ConvexPolyhedron)
    (size : P.vertices.card = 5) (v : P.Vertex) : P.edgeGraphᶜ.degree v ≤ 1 := by
  classical
  letI : P.edgeGraph.LocallyFinite := P.edgeGraph.neighborSetFintype
  have lower : 3 ≤ P.edgeGraph.degree v := by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using P.edgeGraph_min_degree v
  rw [P.edgeGraph.degree_compl, P.vertex_card, size]
  omega

/-- Different missing edges in a five-vertex solid cannot share an endpoint. -/
theorem five_vertices_unique_nonneighbor (P : ConvexPolyhedron) (size : P.vertices.card = 5)
    (a b c : P.Vertex) (ab : a ≠ b) (ac : a ≠ c)
    (missing_ab : ¬ P.edgeGraph.Adj a b) (missing_ac : ¬ P.edgeGraph.Adj a c) : b = c := by
  have count : (P.edgeGraphᶜ.neighborSet a).ncard ≤ 1 := by
    simpa only [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card,
      SimpleGraph.card_neighborSet_eq_degree] using P.five_vertices_complement_degree_le_one size a
  exact (Set.ncard_le_one (Set.toFinite _)).mp count b
    (show b ∈ P.edgeGraphᶜ.neighborSet a from ⟨ab, missing_ab⟩) c
    (show c ∈ P.edgeGraphᶜ.neighborSet a from ⟨ac, missing_ac⟩)

/-- Exactly one or two unordered vertex pairs are missing from the five-vertex edge graph. -/
theorem five_vertices_missing_edge_count (P : ConvexPolyhedron) (size : P.vertices.card = 5) :
    P.edgeGraphᶜ.edgeSet.ncard = 1 ∨ P.edgeGraphᶜ.edgeSet.ncard = 2 := by
  classical
  have degree_sum : ∑ v : P.Vertex, P.edgeGraphᶜ.degree v ≤ 5 := by
    calc
      ∑ v : P.Vertex, P.edgeGraphᶜ.degree v ≤ ∑ _v : P.Vertex, 1 :=
        Finset.sum_le_sum (fun v _ => P.five_vertices_complement_degree_le_one size v)
      _ = 5 := by simp [size]
  have handshake := P.edgeGraphᶜ.sum_degrees_eq_twice_card_edges
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
    at degree_sum handshake
  have count_eq : P.edgeGraphᶜ.edgeSet.ncard = P.edgeGraphᶜ.edgeFinset.card := by
    exact Set.ncard_eq_toFinset_card' P.edgeGraphᶜ.edgeSet
  obtain ⟨a, b, different, missing⟩ := P.five_vertices_have_nonedge size
  have edge : s(a, b) ∈ P.edgeGraphᶜ.edgeSet := ⟨different, missing⟩
  have positive := (show P.edgeGraphᶜ.edgeSet.Nonempty from ⟨s(a, b), edge⟩).ncard_pos
  omega

end SixVertexUnfolding.ConvexPolyhedron
