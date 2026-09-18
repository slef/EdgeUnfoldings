import SixVertexUnfolding.Geometry.BipyramidNonoverlap
import SixVertexUnfolding.Pyramid
import SixVertexUnfolding.Tetrahedron

/-! The complete five-vertex theorem, with no additional geometric hypotheses. -/

namespace SixVertexUnfolding

/-- Every five-vertex convex polyhedron whose original facets are triangles unfolds. -/
theorem every_triangular_five_vertex_polyhedron (P : ConvexPolyhedron)
    (size : P.vertices.card = 5)
    (triangles : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3) :
    P.HasEdgeUnfolding := by
  obtain ⟨B⟩ := P.exists_bipyramid_vertices size triangles
  obtain ⟨net⟩ := B.exists_development triangles 0
  exact net.hasEdgeUnfolding size

/-- Every convex polyhedron with five original vertices has an original-edge unfolding. -/
theorem every_convex_polyhedron_with_five_vertices (P : ConvexPolyhedron)
    (size : P.vertices.card = 5) : P.HasEdgeUnfolding := by
  by_cases triangular : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3
  · exact every_triangular_five_vertex_polyhedron P size triangular
  push Not at triangular
  obtain ⟨F, not_triangle⟩ := triangular
  have lower := F.three_le_vertex_count
  have upper := F.vertex_count_lt
  exact every_five_vertex_polyhedron_with_quadrilateral_face P size F (by omega)

/-- The public theorem is completely proved up to five original vertices. -/
theorem every_convex_polyhedron_with_at_most_five_vertices (P : ConvexPolyhedron)
    (at_most_five : P.vertices.card ≤ 5) : P.HasEdgeUnfolding := by
  rcases P.vertex_count_cases (show P.vertices.card ≤ 6 by omega) with four | five | six
  · exact every_convex_polyhedron_with_four_vertices P four
  · exact every_convex_polyhedron_with_five_vertices P five
  · omega

end SixVertexUnfolding
