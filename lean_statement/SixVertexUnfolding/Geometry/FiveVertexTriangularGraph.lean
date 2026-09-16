import SixVertexUnfolding.Geometry.FacetEdges
import SixVertexUnfolding.Geometry.ExcludedFacets
import SixVertexUnfolding.Geometry.FiveVertexGraphs

/-! With five vertices and triangular facets, precisely one original edge pair is missing. -/

namespace SixVertexUnfolding.ConvexPolyhedron

/-- A triangular five-vertex solid contains four vertices joined pairwise by original edges. -/
theorem five_triangular_has_four_clique (P : ConvexPolyhedron) (size : P.vertices.card = 5)
    (triangles : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3) :
    ∃ s : Set P.Vertex, s.ncard = 4 ∧
      ∀ a ∈ s, ∀ b ∈ s, a ≠ b → P.edgeGraph.Adj a b := by
  obtain ⟨source, universal⟩ := P.at_most_five_has_universal_vertex size.le
  obtain ⟨F, outside⟩ := P.exists_facet_excluding_vertex source
  let base : Set P.Vertex := {v | (v : Space) ∈ F.val}
  have base_count : base.ncard = 3 := by
    have image : Subtype.val '' base = F.val ∩ (P.vertices : Set Space) := by
      ext x
      constructor
      · rintro ⟨v, vF, rfl⟩
        exact ⟨vF, v.property⟩
      · rintro ⟨xF, vertex⟩
        exact ⟨⟨x, vertex⟩, xF, rfl⟩
    rw [← Set.ncard_image_of_injective base Subtype.val_injective, image]
    exact triangles F
  refine ⟨insert source base, ?_, ?_⟩
  · rw [Set.ncard_insert_of_notMem (show source ∉ base from outside), base_count]
  · intro a ha b hb distinct
    rcases ha with rfl | ha
    · exact universal b distinct.symm
    rcases hb with rfl | hb
    · exact P.edgeGraph.symm (universal a distinct)
    · exact F.adjacent_of_triangle (triangles F) a b distinct ha hb

/-- The unique missing pair is the pole pair of the triangular bipyramid graph. -/
theorem five_triangular_unique_missing_pair (P : ConvexPolyhedron) (size : P.vertices.card = 5)
    (triangles : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3) :
    ∃ top bottom : P.Vertex, top ≠ bottom ∧
      ∀ a b : P.Vertex, P.edgeGraph.Adj a b ↔ a ≠ b ∧ s(a, b) ≠ s(top, bottom) := by
  obtain ⟨clique, count, adjacent⟩ := P.five_triangular_has_four_clique size triangles
  have one : cliqueᶜ.ncard = 1 := by
    have total := Set.ncard_add_ncard_compl clique
    have total_five : clique.ncard + cliqueᶜ.ncard = 5 := by
      simpa only [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] using
        (total.trans (by simp [Nat.card_eq_fintype_card, size] : Nat.card P.Vertex = 5))
    omega
  obtain ⟨pole, complement⟩ := Set.ncard_eq_one.mp one
  have mem_clique (v : P.Vertex) (different : v ≠ pole) : v ∈ clique := by
    by_contra outside
    have equal : v ∈ ({pole} : Set P.Vertex) := complement ▸ outside
    exact different equal
  have touches_pole (a b : P.Vertex) (different : a ≠ b) (missing : ¬ P.edgeGraph.Adj a b) :
      a = pole ∨ b = pole := by
    by_contra neither
    push Not at neither
    exact missing (adjacent a (mem_clique a neither.1) b (mem_clique b neither.2) different)
  obtain ⟨a, b, ab, missing⟩ := P.five_vertices_have_nonedge size
  have partner : ∃ q : P.Vertex, pole ≠ q ∧ ¬ P.edgeGraph.Adj pole q := by
    rcases touches_pole a b ab missing with rfl | rfl
    · exact ⟨b, ab, missing⟩
    · exact ⟨a, ab.symm, fun edge => missing (P.edgeGraph.symm edge)⟩
  obtain ⟨other, different, not_edge⟩ := partner
  refine ⟨pole, other, different, ?_⟩
  intro a b
  constructor
  · intro edge
    refine ⟨edge.ne, ?_⟩
    intro same
    rcases Sym2.eq_iff.mp same with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact not_edge edge
    · exact not_edge (P.edgeGraph.symm edge)
  · rintro ⟨ab, pair_different⟩
    by_contra missing
    rcases touches_pole a b ab missing with equal | equal
    · subst a
      have same := P.five_vertices_unique_nonneighbor size pole b other ab different missing not_edge
      exact pair_different (by rw [same])
    · subst b
      have same := P.five_vertices_unique_nonneighbor size pole a other ab.symm different
        (fun edge => missing (P.edgeGraph.symm edge)) not_edge
      exact pair_different (by rw [same, Sym2.eq_swap])

end SixVertexUnfolding.ConvexPolyhedron
