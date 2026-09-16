import SixVertexUnfolding.Geometry.CutTreeRadialPartition
import SixVertexUnfolding.Geometry.SmallPolyhedronCutEdgeStrips
import SixVertexUnfolding.Geometry.SmallPolyhedronCutRetraction
import SixVertexUnfolding.Geometry.SmallPolyhedronCutTree
import SixVertexUnfolding.Geometry.SmallPolyhedronCutTreeVertexRays
import SixVertexUnfolding.Geometry.SmallPolyhedronRouteStrips

/-! A finite radial partition of the actual surface into tree-vertex rays
and the two strips attached to each open tree edge. The cut set and source
are included explicitly; no Euclidean development is assumed here.

Here the shortest-route inputs come from the actual vertex fans of a
polyhedron with at most six vertices and triangular/quadrilateral faces.
No canonical graph model is assumed. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

variable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include size small_faces in
/-- Vertex rays are precisely the boundaries excluded from open-edge strips. -/
theorem small_vertex_rays_disjoint_strips (a : frontier P.body) (T : P.CutLocusTree a)
    {u v : T.vertices} (edge : T.graph.Adj u v) (S : CutEdgeStrips T edge) :
    Disjoint T.vertexRays (routeStrip S.first ∪ routeStrip S.second) := by
  apply disjoint_left.mpr
  intro b ray strip
  have different : b ≠ a := by
    rcases strip with first | second
    · exact (small_routeStrip_outside_cutSet size small_faces a _
        (fun t => T.open_edge_cut edge _ (T.openEdgeTarget_inside edge t)) S.first S.first_member b first).1
    · exact (small_routeStrip_outside_cutSet size small_faces a _
        (fun t => T.open_edge_cut edge _ (T.openEdgeTarget_inside edge t)) S.second S.second_member b second).1
  have vertex := (small_vertex_rays_iff_endpoint size small_faces a T b different).mp ray
  have inside := (small_cut_edge_strips_iff_endpoint size small_faces a T edge S b different).mp strip
  exact disjoint_left.mp (T.no_vertex_inside u v edge) inside.2 vertex.2

include size small_faces in
/-- Once two branches are chosen for each edge, the resulting regions cover the actual boundary. -/
theorem small_cut_tree_radial_partition (a : frontier P.body) (T : P.CutLocusTree a)
    (strips : ∀ u v : T.vertices, ∀ edge : T.graph.Adj u v, CutEdgeStrips T edge)
    (b : frontier P.body) : b = a ∨ b ∈ P.cutSet a ∨ b ∈ T.vertexRays ∨
      ∃ u v : T.vertices, ∃ edge : T.graph.Adj u v,
        b ∈ routeStrip (strips u v edge).first ∪ routeStrip (strips u v edge).second := by
  by_cases source : b = a
  · exact Or.inl source
  right
  by_cases cut : b ∈ P.cutSet a
  · exact Or.inl cut
  right
  let endpoint := small_cutEndpoint size small_faces a ⟨b, source⟩
  have trace : (endpoint.val : Space) ∈ P.cutSetInSpace a := ⟨endpoint.val, endpoint.property, rfl⟩
  rcases (T.trace _).mp trace with vertex | ⟨u, v, edge, inside⟩
  · exact Or.inl ((small_vertex_rays_iff_endpoint size small_faces a T b source).mpr ⟨cut, vertex⟩)
  · exact Or.inr ⟨u, v, edge,
      (small_cut_edge_strips_iff_endpoint size small_faces a T edge (strips u v edge) b source).mpr ⟨cut, inside⟩⟩

include size small_faces in
/-- The finite tree and every strip family can be constructed simultaneously. -/
theorem small_exists_cut_tree_radial_partition (a : frontier P.body) :
    ∃ T : P.CutLocusTree a,
      ∃ strips : ∀ u v : T.vertices, ∀ edge : T.graph.Adj u v, CutEdgeStrips T edge,
        ∀ b : frontier P.body, b = a ∨ b ∈ P.cutSet a ∨ b ∈ T.vertexRays ∨
          ∃ u v : T.vertices, ∃ edge : T.graph.Adj u v,
            b ∈ routeStrip (strips u v edge).first ∪ routeStrip (strips u v edge).second := by
  classical
  obtain ⟨T⟩ := small_exists_regular_cut_tree size small_faces a
  let strips (u v : T.vertices) (edge : T.graph.Adj u v) : CutEdgeStrips T edge :=
    Classical.choice (small_exists_cut_edge_strips size small_faces a T edge)
  exact ⟨T, strips, small_cut_tree_radial_partition size small_faces a T strips⟩

end SixVertexUnfolding.ConvexPolyhedron
