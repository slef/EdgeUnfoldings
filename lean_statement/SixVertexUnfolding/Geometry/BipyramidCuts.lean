import SixVertexUnfolding.Geometry.BipyramidTree

/-! The four cut edges at the equator source form an original vertex spanning tree. -/

namespace SixVertexUnfolding

/-- The four-edge star on five concrete vertex indices. -/
def fiveVertexStar (source : Fin 5) : SimpleGraph (Fin 5) where
  Adj a b := a ≠ b ∧ (a = source ∨ b = source)
  symm := fun _ _ edge => ⟨edge.1.symm, edge.2.symm⟩
  loopless := ⟨fun _ edge => edge.1 rfl⟩

instance (source : Fin 5) : DecidableRel (fiveVertexStar source).Adj := by
  unfold fiveVertexStar
  infer_instance

theorem fiveVertexStar_isTree (source : Fin 5) : (fiveVertexStar source).IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  constructor
  · rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨source, ?_⟩
    intro i
    by_cases same : source = i
    · subst i
      exact SimpleGraph.Reachable.rfl
    · exact (show (fiveVertexStar source).Adj source i from ⟨same, Or.inl rfl⟩).reachable
  · rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, Nat.card_eq_fintype_card]
    fin_cases source <;> decide

namespace ConvexPolyhedron.BipyramidVertices

variable {P : ConvexPolyhedron} (B : BipyramidVertices P)

/-- Every equator vertex is joined by an original edge to every other original vertex. -/
theorem equator_universal (source : Fin 3) (v : P.Vertex) (different : v ≠ B.equatorVertex source) :
    P.edgeGraph.Adj (B.equatorVertex source) v := by
  rcases B.vertex_cases v with top | bottom | ⟨i, equator⟩
  · rw [top]
    exact P.edgeGraph.symm (B.top_equator_adjacent source)
  · rw [bottom]
    exact P.edgeGraph.symm (B.bottom_equator_adjacent source)
  · rw [equator]
    exact B.equator_adjacent source i (fun same => different (equator.trans (congrArg B.equatorVertex same.symm)))

/-- Cutting exactly the four source edges cuts a spanning tree of the original vertex-edge graph. -/
theorem exists_source_cut_tree (size : P.vertices.card = 5) (source : Fin 3) :
    ∃ cuts : SimpleGraph P.Vertex, cuts.IsTree ∧
      ∀ a b, cuts.Adj a b ↔ P.edgeGraph.Adj a b ∧
        (a = B.equatorVertex source ∨ b = B.equatorVertex source) := by
  let index : Fin 5 ≃ P.Vertex := (Fintype.equivFinOfCardEq (P.vertex_card.trans size)).symm
  let center := index.symm (B.equatorVertex source)
  let cuts := (fiveVertexStar center).comap index.symm
  have tree : cuts.IsTree :=
    (SimpleGraph.Iso.comap index.symm (fiveVertexStar center)).isTree_iff.mpr
      (fiveVertexStar_isTree center)
  refine ⟨cuts, tree, ?_⟩
  intro a b
  change (index.symm a ≠ index.symm b ∧
    (index.symm a = index.symm (B.equatorVertex source) ∨
      index.symm b = index.symm (B.equatorVertex source))) ↔ _
  simp only [ne_eq, index.symm.injective.eq_iff]
  constructor
  · rintro ⟨different, at_source⟩
    refine ⟨?_, at_source⟩
    rcases at_source with left | right
    · subst a
      exact B.equator_universal source b (fun same => different same.symm)
    · subst b
      exact P.edgeGraph.symm (B.equator_universal source a different)
  · rintro ⟨edge, at_source⟩
    exact ⟨edge.ne, at_source⟩

end ConvexPolyhedron.BipyramidVertices
end SixVertexUnfolding
