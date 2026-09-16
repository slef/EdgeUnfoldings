import SixVertexUnfolding.Geometry.CutTreeTriangleCoverage
import SixVertexUnfolding.Geometry.SmallPolyhedronCutEdgeTriangles
import SixVertexUnfolding.Geometry.SmallPolyhedronCutTreeRadialPartition
import SixVertexUnfolding.Geometry.SmallPolyhedronCutTreeStripDensity

/-! The finitely many closed radial triangles cover the actual whole
boundary, including all exceptional rays and cut points. This coverage
does not identify the distinct copies needed in a later cut surface.

Here the shortest-route inputs come from the actual vertex fans of a
polyhedron with at most six vertices and triangular/quadrilateral faces.
No canonical graph model is assumed. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

variable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include size small_faces in
/-- Any choices of the actual paired developments cover the entire boundary. -/
theorem small_cut_tree_triangles_cover (a : frontier P.body) (T : P.CutLocusTree a)
    (triangles : (d : T.graph.Dart) → CutEdgeTriangles T d.adj) (b : frontier P.body) :
    ∃ d, b ∈ range (closedRouteStripMap (triangles d).first) ∪
      range (closedRouteStripMap (triangles d).second) := by
  classical
  letI : Fintype T.vertices := T.finite_vertices.fintype
  let covered : Set (frontier P.body) := ⋃ d,
    range (closedRouteStripMap (triangles d).first) ∪ range (closedRouteStripMap (triangles d).second)
  have closed : IsClosed covered := isClosed_iUnion_of_finite (fun d =>
    (isCompact_range (closedRouteStripMap (triangles d).first).continuous).isClosed.union
      (isCompact_range (closedRouteStripMap (triangles d).second).continuous).isClosed)
  have included : {x : frontier P.body | x ≠ a ∧ x ∉ P.cutSet a ∧ x ∉ T.vertexRays} ⊆ covered := by
    intro x hx
    rcases small_cut_tree_radial_partition size small_faces a T
        (fun u v edge => (triangles ⟨(u, v), edge⟩).strips) x with
      source | cut | ray | ⟨u, v, edge, inside⟩
    · exact (hx.1 source).elim
    · exact (hx.2.1 cut).elim
    · exact (hx.2.2 ray).elim
    · apply mem_iUnion.mpr
      refine ⟨⟨(u, v), edge⟩, ?_⟩
      rcases inside with first | second
      · left
        rw [← closure_routeStrip_eq _ _ (fun t => (triangles ⟨(u, v), edge⟩).agrees t |>.1)]
        exact subset_closure first
      · right
        rw [← closure_routeStrip_eq _ _ (fun t => (triangles ⟨(u, v), edge⟩).agrees t |>.2)]
        exact subset_closure second
  have all := closure_minimal included closed
  rw [(small_cut_tree_strip_points_dense size small_faces a T).closure_eq] at all
  exact mem_iUnion.mp (all (mem_univ b))

include size small_faces in
/-- Choose all actual paired developments simultaneously, with complete surface coverage. -/
theorem small_exists_cut_tree_triangle_cover (a : frontier P.body) (T : P.CutLocusTree a) :
    ∃ triangles : (d : T.graph.Dart) → CutEdgeTriangles T d.adj,
      ∀ b : frontier P.body, ∃ d,
        b ∈ range (closedRouteStripMap (triangles d).first) ∪
          range (closedRouteStripMap (triangles d).second) := by
  classical
  let triangles (d : T.graph.Dart) : CutEdgeTriangles T d.adj :=
    Classical.choice (small_exists_cut_edge_triangles size small_faces a T d.adj)
  exact ⟨triangles, small_cut_tree_triangles_cover size small_faces a T triangles⟩

end SixVertexUnfolding.ConvexPolyhedron
