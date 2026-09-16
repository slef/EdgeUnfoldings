import SixVertexUnfolding.Geometry.OppositePairs
import SixVertexUnfolding.Geometry.SixVertexCuts
import SixVertexUnfolding.PairedGraphClassification

/-! The four remaining original vertex-edge graphs, obtained from the geometric polyhedron. -/

namespace SixVertexUnfolding.ConvexPolyhedron

/-- A canonical graph name and concrete labels for all six original vertices. -/
structure SixVertexGraph (P : ConvexPolyhedron) where
  kind : SmallGraphs.SixGraphKind
  vertex : Fin 6 ≃ P.Vertex
  edges : ∀ i j : Fin 6, P.edgeGraph.Adj (vertex i) (vertex j) ↔
    i ≠ j ∧ s(i, j) ∉ kind.missingEdges

/-- Every remaining six-vertex graph without a universal vertex has one of the four canonical forms. -/
theorem exists_six_vertex_graph (P : ConvexPolyhedron) (size : P.vertices.card = 6)
    (no_universal : ¬ ∃ v : P.Vertex, ∀ w, w ≠ v → P.edgeGraph.Adj v w)
    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4) : Nonempty P.SixVertexGraph := by
  classical
  obtain ⟨pairs⟩ := P.exists_opposite_pairs size no_universal small_faces
  let standard : (Bool × Fin 3) ≃ Fin 6 := Equiv.ofBijective (SmallGraphs.pairingChoices 0)
    (SmallGraphs.pairingChoices_bijective 0)
  let index : Fin 6 ≃ P.Vertex := standard.symm.trans pairs.vertex
  let graph := P.edgeGraphᶜ.comap index
  have index_pair (side : Bool) (i : Fin 3) : index (standard (side, i)) = pairs.vertex (side, i) := by
    simp [index]
  have matched (i : Fin 3) : graph.Adj (standard (false, i)) (standard (true, i)) := by
    change index (standard (false, i)) ≠ index (standard (true, i)) ∧
      ¬ P.edgeGraph.Adj (index (standard (false, i))) (index (standard (true, i)))
    rw [index_pair, index_pair]
    refine ⟨?_, pairs.nonedge i⟩
    intro same
    have impossible := congrArg Prod.fst (pairs.vertex.injective same)
    cases impossible
  have no_three (a b c d : Fin 6) (ab : graph.Adj a b) (ac : graph.Adj a c) (ad : graph.Adj a d) :
      b = c ∨ b = d ∨ c = d := by
    rcases P.six_vertices_no_three_nonneighbors size no_universal (index a) (index b) (index c) (index d)
        ab ac ad with same | same | same
    exacts [Or.inl (index.injective same), Or.inr (Or.inl (index.injective same)),
      Or.inr (Or.inr (index.injective same))]
  have no_square (labels : Fin 6 ≃ Fin 6) :
      ¬ (graph.Adj (labels 0) (labels 2) ∧ graph.Adj (labels 0) (labels 3) ∧
        graph.Adj (labels 1) (labels 2) ∧ graph.Adj (labels 1) (labels 3)) :=
    P.no_complement_square (labels.trans index)
  obtain ⟨k, classified⟩ := SmallGraphs.classify_paired_graph graph
    (matched 0) (matched 1) (matched 2) no_three no_square
  let labels : Fin 6 ≃ Fin 6 := Equiv.ofBijective (SmallGraphs.pairedGraphChoices k).2
    (SmallGraphs.pairedGraphChoices_bijective k)
  refine ⟨{
    kind := (SmallGraphs.pairedGraphChoices k).1
    vertex := labels.trans index
    edges := ?_
  }⟩
  intro i j
  have nonedges := classified i j
  change P.edgeGraphᶜ.Adj (index (labels i)) (index (labels j)) ↔ _ at nonedges
  change P.edgeGraph.Adj (index (labels i)) (index (labels j)) ↔ _
  rw [SimpleGraph.compl_adj] at nonedges
  have distinct : index (labels i) ≠ index (labels j) ↔ i ≠ j := by
    simp only [index.injective.ne_iff, labels.injective.ne_iff]
  rw [distinct] at nonedges
  constructor
  · intro edge
    exact ⟨fun same => edge.ne (same ▸ rfl), fun missing => (nonedges.mpr missing).2 edge⟩
  · rintro ⟨different, not_missing⟩
    by_contra not_edge
    exact not_missing (nonedges.mp ⟨different, not_edge⟩)

end SixVertexUnfolding.ConvexPolyhedron
