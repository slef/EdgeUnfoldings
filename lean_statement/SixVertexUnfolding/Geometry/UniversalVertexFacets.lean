import SixVertexUnfolding.Geometry.QuadrilateralEdges

/-! A universal vertex cannot belong to a quadrilateral facet: its
opposite corner would be joined to it by a forbidden original diagonal. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- Every small facet incident to a universal vertex is triangular. -/
theorem universal_vertex_facets_triangular (P : ConvexPolyhedron)
    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4)
    (v : P.Vertex) (universal : ∀ w : P.Vertex, w ≠ v → P.edgeGraph.Adj v w)
    (F : P.Face) (incident : (v : Space) ∈ F.val) :
    (F.val ∩ (P.vertices : Set Space)).ncard = 3 := by
  rcases small_faces F with triangle | quadrilateral
  · exact triangle
  · obtain ⟨Q⟩ := F.exists_quadrilateral quadrilateral
    have vertex : (v : Space) ∈ Set.range (fun i => (Q.corner i : Space)) := by
      rw [← Q.vertices]
      exact ⟨incident, v.property⟩
    obtain ⟨i, same⟩ := vertex
    have at_corner : Q.corner i = v := Subtype.ext same
    have opposite : Q.corner (i + 2) ≠ v := by
      intro equal
      have impossible := Q.distinct (equal.trans at_corner.symm)
      fin_cases i <;> simp_all
    exact (Q.diagonal_not_adjacent i (at_corner.symm ▸ universal _ opposite)).elim

end SixVertexUnfolding.ConvexPolyhedron
