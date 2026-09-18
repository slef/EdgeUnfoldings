import SixVertexUnfolding.Tetrahedron
import SixVertexUnfolding.Pyramid
import SixVertexUnfolding.Bipyramid

/-! Separate the completed cases from the precise face sizes still requiring an unfolding. -/

namespace SixVertexUnfolding

/-- A five-vertex solid is already unfolded unless every original facet is triangular. -/
theorem five_vertex_reduction (P : ConvexPolyhedron) (size : P.vertices.card = 5) :
    P.HasEdgeUnfolding ∨ ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 := by
  by_cases triangular : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3
  · exact Or.inr triangular
  push Not at triangular
  obtain ⟨F, not_triangle⟩ := triangular
  have lower := F.three_le_vertex_count
  have upper := F.vertex_count_lt
  exact Or.inl (every_five_vertex_polyhedron_with_quadrilateral_face P size F (by omega))

/-- A six-vertex solid is already unfolded unless its facets are triangles and quadrilaterals. -/
theorem six_vertex_reduction (P : ConvexPolyhedron) (size : P.vertices.card = 6) :
    P.HasEdgeUnfolding ∨ ∀ F : P.Face,
      (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4 := by
  by_cases small : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4
  · exact Or.inr small
  push Not at small
  obtain ⟨F, not_triangle, not_quadrilateral⟩ := small
  have lower := F.three_le_vertex_count
  have upper := F.vertex_count_lt
  exact Or.inl (every_six_vertex_polyhedron_with_pentagonal_face P size F (by omega))

/-- The completed constructions leave only six vertices with triangular or quadrilateral facets. -/
theorem unfolding_or_remaining_cases (P : ConvexPolyhedron) (at_most_six : P.vertices.card ≤ 6) :
    P.HasEdgeUnfolding ∨
      (P.vertices.card = 6 ∧ ∀ F : P.Face,
        (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
        (F.val ∩ (P.vertices : Set Space)).ncard = 4) := by
  rcases P.vertex_count_cases at_most_six with four | five | six
  · exact Or.inl (every_convex_polyhedron_with_four_vertices P four)
  · exact Or.inl (every_convex_polyhedron_with_five_vertices P five)
  · rcases six_vertex_reduction P six with unfolded | small_faces
    · exact Or.inl unfolded
    · exact Or.inr ⟨six, small_faces⟩

end SixVertexUnfolding
