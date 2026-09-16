import SixVertexUnfolding.Geometry.CutEdgeTriangles
import SixVertexUnfolding.Geometry.SmallPolyhedronCutEdgeStrips
import SixVertexUnfolding.Geometry.SmallPolyhedronCutEdgeTriangleDevelopments

/-! Keep the two actual radial developments of a cut edge together.
All fields are supplied by the existing geometric constructions.

Here the shortest-route inputs come from the actual vertex fans of a
polyhedron with at most six vertices and triangular/quadrilateral faces.
No canonical graph model is assumed. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

variable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include size small_faces in
/-- Both complete radial triangles exist for every actual cut-tree edge. -/
theorem small_exists_cut_edge_triangles (a : frontier P.body) (T : P.CutLocusTree a)
    {u v : T.vertices} (edge : T.graph.Adj u v) : Nonempty (CutEdgeTriangles T edge) := by
  obtain ⟨strips⟩ := small_exists_cut_edge_strips size small_faces a T edge
  obtain ⟨model, first, second, agrees, member, ⟨D⟩, ⟨E⟩⟩ :=
    small_exists_cut_edge_triangle_developments size small_faces a T edge strips
  exact ⟨⟨strips, model, first, second, agrees, member, D, E⟩⟩

end SixVertexUnfolding.ConvexPolyhedron
