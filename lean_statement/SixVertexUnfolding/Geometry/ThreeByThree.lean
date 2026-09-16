import SixVertexUnfolding.Geometry.FacetColoring

/-! Concrete labels for two triples with all nine cross-edges present. -/

namespace SixVertexUnfolding.ConvexPolyhedron

/-- Two triples of original vertices, with every cross-pair joined by an original edge. -/
structure ThreeByThree (P : ConvexPolyhedron) where
  vertex : (Bool × Fin 3) ≃ P.Vertex
  across : ∀ i j : Fin 3, P.edgeGraph.Adj (vertex (false, i)) (vertex (true, j))

namespace ThreeByThree

variable {P : ConvexPolyhedron} (B : P.ThreeByThree)

/-- The two triples give the two vertex colors. -/
def color (v : P.Vertex) : Bool := (B.vertex.symm v).1

@[simp] theorem color_vertex (side : Bool) (i : Fin 3) : B.color (B.vertex (side, i)) = side := by
  simp [color]

theorem adjacent_of_different_color (a b : P.Vertex) (different : B.color a ≠ B.color b) :
    P.edgeGraph.Adj a b := by
  obtain ⟨⟨side, i⟩, rfl⟩ := B.vertex.surjective a
  obtain ⟨⟨other, j⟩, rfl⟩ := B.vertex.surjective b
  simp only [B.color_vertex] at different
  cases side <;> cases other
  · exact False.elim (different rfl)
  · exact B.across i j
  · exact (B.across j i).symm
  · exact False.elim (different rfl)

/-- A color class contains only three vertices. -/
theorem no_four_same_color (v : Fin 4 → P.Vertex) (distinct : Function.Injective v) :
    ¬ ∀ i : Fin 4, B.color (v i) = B.color (v 0) := by
  intro same
  have injective : Function.Injective (fun i : Fin 4 => (B.vertex.symm (v i)).2) := by
    intro i j equal
    apply distinct
    apply B.vertex.symm.injective
    apply Prod.ext
    · exact (same i).trans (same j).symm
    · exact equal
  have impossible := Fintype.card_le_of_injective _ injective
  norm_num at impossible

/-- A same-color triangle would give a universal original vertex. -/
theorem no_monochromatic_triangle
    (no_universal : ¬ ∃ v : P.Vertex, ∀ w, w ≠ v → P.edgeGraph.Adj v w)
    (a b c : P.Vertex) (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c)
    (edge_ab : P.edgeGraph.Adj a b) (edge_ac : P.edgeGraph.Adj a c) :
    ¬ (B.color a = B.color b ∧ B.color b = B.color c) := by
  rintro ⟨same_ab, same_bc⟩
  apply no_universal
  refine ⟨a, ?_⟩
  intro w wa
  by_cases different : B.color a ≠ B.color w
  · exact B.adjacent_of_different_color a w different
  have same_aw : B.color a = B.color w := not_not.mp different
  by_cases wb : w = b
  · exact wb ▸ edge_ab
  by_cases wc : w = c
  · exact wc ▸ edge_ac
  apply False.elim
  let four : Fin 4 → P.Vertex := ![a, b, c, w]
  have injective : Function.Injective four := by
    intro i j same
    fin_cases i <;> fin_cases j <;> simp [four] at same ⊢ <;> grind
  apply B.no_four_same_color four injective
  intro i
  fin_cases i
  · rfl
  · exact same_ab.symm
  · exact (same_ab.trans same_bc).symm
  · exact same_aw.symm

/-- The nine cross-pairs are all distinct unordered original edges. -/
theorem cross_pair_injective :
    Function.Injective (fun ij : Fin 3 × Fin 3 => s(B.vertex (false, ij.1), B.vertex (true, ij.2))) := by
  intro ij kl same
  rcases Sym2.eq_iff.mp same with ⟨left, right⟩ | ⟨swapped, _⟩
  · apply Prod.ext
    · exact congrArg (fun p : Bool × Fin 3 => p.2) (B.vertex.injective left)
    · exact congrArg (fun p : Bool × Fin 3 => p.2) (B.vertex.injective right)
  · have impossible := congrArg Prod.fst (B.vertex.injective swapped)
    cases impossible

/-- The cross-color original edges form exactly the product of the two triples. -/
theorem cross_edgeFinset :
    P.originalEdges.filter (fun e => internalEdgeWeight B.color e = 0) =
      Finset.univ.image (fun ij : Fin 3 × Fin 3 => s(B.vertex (false, ij.1), B.vertex (true, ij.2))) := by
  classical
  ext e
  induction e using Sym2.inductionOn with
  | hf a b =>
    obtain ⟨⟨side, i⟩, rfl⟩ := B.vertex.surjective a
    obtain ⟨⟨other, j⟩, rfl⟩ := B.vertex.surjective b
    simp only [Finset.mem_filter, mem_originalEdges, SimpleGraph.mem_edgeSet,
      internalEdgeWeight_pair, B.color_vertex]
    cases side <;> cases other
    · simp only [↓reduceIte, one_ne_zero, and_false, false_iff]
      intro member
      obtain ⟨⟨k, l⟩, _, pair⟩ := Finset.mem_image.mp member
      rcases Sym2.eq_iff.mp pair with ⟨_, same⟩ | ⟨_, same⟩
      all_goals have impossible := congrArg Prod.fst (B.vertex.injective same); cases impossible
    · constructor
      · intro _
        exact Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩
      · intro _
        exact ⟨B.across i j, by decide⟩
    · constructor
      · intro _
        exact Finset.mem_image.mpr ⟨(j, i), Finset.mem_univ _, Sym2.eq_swap⟩
      · intro _
        exact ⟨(B.across j i).symm, by decide⟩
    · simp only [↓reduceIte, one_ne_zero, and_false, false_iff]
      intro member
      obtain ⟨⟨k, l⟩, _, pair⟩ := Finset.mem_image.mp member
      rcases Sym2.eq_iff.mp pair with ⟨same, _⟩ | ⟨same, _⟩
      all_goals have impossible := congrArg Prod.fst (B.vertex.injective same); cases impossible

/-- There are exactly nine cross-color original edges. -/
theorem cross_edge_count :
    (P.originalEdges.filter (fun e => internalEdgeWeight B.color e = 0)).card = 9 := by
  classical
  rw [B.cross_edgeFinset, Finset.card_image_of_injective _ B.cross_pair_injective]
  simp

/-- All other original edges lie within a triple; there are nine cross-edges in addition. -/
theorem total_edge_count :
    (∑ e ∈ P.originalEdges, internalEdgeWeight B.color e) + 9 = P.originalEdges.card := by
  classical
  rw [← B.cross_edge_count]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr
  · ext e
    simp
  · intro e _
    induction e using Sym2.inductionOn with
    | hf a b =>
      simp only [internalEdgeWeight_pair]
      by_cases same : B.color a = B.color b <;> simp [same]

end ThreeByThree
end SixVertexUnfolding.ConvexPolyhedron
