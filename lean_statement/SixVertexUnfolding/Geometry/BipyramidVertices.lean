import SixVertexUnfolding.Geometry.FiveVertexTriangularGraph

/-! Name the two poles and three equator vertices of the remaining five-vertex graph. -/

namespace SixVertexUnfolding.ConvexPolyhedron

/-- The two poles form the unique missing edge; the equator lists the other three vertices once. -/
structure BipyramidVertices (P : ConvexPolyhedron) where
  top : P.Vertex
  bottom : P.Vertex
  distinct_poles : top ≠ bottom
  equator : Fin 3 ≃ {v : P.Vertex // v ≠ top ∧ v ≠ bottom}
  edges : ∀ a b : P.Vertex, P.edgeGraph.Adj a b ↔ a ≠ b ∧ s(a, b) ≠ s(top, bottom)

/-- Every five-vertex solid with triangular facets admits these concrete vertex names. -/
theorem exists_bipyramid_vertices (P : ConvexPolyhedron) (size : P.vertices.card = 5)
    (triangles : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3) :
    Nonempty (BipyramidVertices P) := by
  classical
  obtain ⟨top, bottom, distinct, edges⟩ := P.five_triangular_unique_missing_pair size triangles
  let E : Set P.Vertex := {v | v ≠ top ∧ v ≠ bottom}
  have set_eq : E = Set.univ \ {top, bottom} := by ext v; simp [E]
  have count : Fintype.card E = 3 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, set_eq,
      Set.ncard_diff (Set.subset_univ _), Set.ncard_univ, Set.ncard_pair distinct]
    simp [Nat.card_eq_fintype_card, size]
  exact ⟨⟨top, bottom, distinct, (Fintype.equivFinOfCardEq count).symm, edges⟩⟩

namespace BipyramidVertices

variable {P : ConvexPolyhedron} (B : BipyramidVertices P)

/-- Equator vertices, regarded as original vertices of the solid. -/
def equatorVertex (i : Fin 3) : P.Vertex := B.equator i

theorem equator_injective : Function.Injective B.equatorVertex := by
  intro i j same
  exact B.equator.injective (Subtype.ext same)

theorem equator_ne_top (i : Fin 3) : B.equatorVertex i ≠ B.top := (B.equator i).property.1

theorem equator_ne_bottom (i : Fin 3) : B.equatorVertex i ≠ B.bottom := (B.equator i).property.2

/-- Every vertex is one of the two poles or one of the three equator vertices. -/
theorem vertex_cases (v : P.Vertex) : v = B.top ∨ v = B.bottom ∨ ∃ i, v = B.equatorVertex i := by
  by_cases top : v = B.top
  · exact Or.inl top
  by_cases bottom : v = B.bottom
  · exact Or.inr (Or.inl bottom)
  obtain ⟨i, equal⟩ := B.equator.surjective ⟨v, top, bottom⟩
  exact Or.inr (Or.inr ⟨i, (congrArg Subtype.val equal).symm⟩)

theorem poles_not_adjacent : ¬ P.edgeGraph.Adj B.top B.bottom := by simp [B.edges]

theorem top_equator_adjacent (i : Fin 3) : P.edgeGraph.Adj B.top (B.equatorVertex i) := by
  apply (B.edges _ _).mpr
  refine ⟨(B.equator_ne_top i).symm, ?_⟩
  intro same
  rcases Sym2.eq_iff.mp same with ⟨_, equal⟩ | ⟨equal, _⟩
  · exact B.equator_ne_bottom i equal
  · exact B.distinct_poles equal

theorem bottom_equator_adjacent (i : Fin 3) : P.edgeGraph.Adj B.bottom (B.equatorVertex i) := by
  apply (B.edges _ _).mpr
  refine ⟨(B.equator_ne_bottom i).symm, ?_⟩
  intro same
  rcases Sym2.eq_iff.mp same with ⟨equal, _⟩ | ⟨_, equal⟩
  · exact B.distinct_poles equal.symm
  · exact B.equator_ne_top i equal

theorem equator_adjacent (i j : Fin 3) (different : i ≠ j) :
    P.edgeGraph.Adj (B.equatorVertex i) (B.equatorVertex j) := by
  apply (B.edges _ _).mpr
  refine ⟨fun same => different (B.equator_injective same), ?_⟩
  intro same
  rcases Sym2.eq_iff.mp same with ⟨equal, _⟩ | ⟨equal, _⟩
  · exact B.equator_ne_top i equal
  · exact B.equator_ne_bottom i equal

/-- Choose the upper or lower pole; the Boolean is just a two-element face index. -/
def poleVertex (upper : Bool) : P.Vertex := if upper then B.top else B.bottom

theorem pole_ne_equator (upper : Bool) (i : Fin 3) : B.poleVertex upper ≠ B.equatorVertex i := by
  cases upper
  · exact (B.equator_ne_bottom i).symm
  · exact (B.equator_ne_top i).symm

theorem pole_ne_opposite (upper : Bool) : B.poleVertex upper ≠ B.poleVertex (!upper) := by
  cases upper
  · exact B.distinct_poles.symm
  · exact B.distinct_poles

theorem pole_opposite_not_adjacent (upper : Bool) :
    ¬ P.edgeGraph.Adj (B.poleVertex upper) (B.poleVertex (!upper)) := by
  cases upper
  · exact fun edge => B.poles_not_adjacent (P.edgeGraph.symm edge)
  · exact B.poles_not_adjacent

theorem pole_equator_adjacent (upper : Bool) (i : Fin 3) :
    P.edgeGraph.Adj (B.poleVertex upper) (B.equatorVertex i) := by
  cases upper
  · exact B.bottom_equator_adjacent i
  · exact B.top_equator_adjacent i

theorem vertex_cases_from_pole (upper : Bool) (v : P.Vertex) :
    v = B.poleVertex upper ∨ v = B.poleVertex (!upper) ∨ ∃ i, v = B.equatorVertex i := by
  cases upper
  · simpa only [poleVertex, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_eq,
      or_comm, or_left_comm] using B.vertex_cases v
  · exact B.vertex_cases v

end BipyramidVertices
end SixVertexUnfolding.ConvexPolyhedron
