import SixVertexUnfolding.Geometry.CutTreeVertexRays
import SixVertexUnfolding.Geometry.ClosedCutEdgeRoutes

/-! A finite radial partition of the actual surface into tree-vertex rays
and the two strips attached to each open tree edge. The cut set and source
are included explicitly; no Euclidean development is assumed here. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- Vertex rays are precisely the boundaries excluded from open-edge strips. -/
theorem vertex_rays_disjoint_strips (a : frontier P.body) (T : P.CutLocusTree a)
    {u v : T.vertices} (edge : T.graph.Adj u v) (S : CutEdgeStrips T edge) :
    Disjoint T.vertexRays (routeStrip S.first ∪ routeStrip S.second) := by
  apply disjoint_left.mpr
  intro b ray strip
  have different : b ≠ a := by
    rcases strip with first | second
    · exact (graph.routeStrip_outside_cutSet small_faces a _
        (fun t => T.open_edge_cut edge _ (T.openEdgeTarget_inside edge t)) S.first S.first_member b first).1
    · exact (graph.routeStrip_outside_cutSet small_faces a _
        (fun t => T.open_edge_cut edge _ (T.openEdgeTarget_inside edge t)) S.second S.second_member b second).1
  have vertex := (graph.vertex_rays_iff_endpoint small_faces a T b different).mp ray
  have inside := (graph.cut_edge_strips_iff_endpoint small_faces a T edge S b different).mp strip
  exact disjoint_left.mp (T.no_vertex_inside u v edge) inside.2 vertex.2

include graph small_faces in
/-- Once two branches are chosen for each edge, the resulting regions cover the actual boundary. -/
theorem cut_tree_radial_partition (a : frontier P.body) (T : P.CutLocusTree a)
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
  let endpoint := graph.cutEndpoint small_faces a ⟨b, source⟩
  have trace : (endpoint.val : Space) ∈ P.cutSetInSpace a := ⟨endpoint.val, endpoint.property, rfl⟩
  rcases (T.trace _).mp trace with vertex | ⟨u, v, edge, inside⟩
  · exact Or.inl ((graph.vertex_rays_iff_endpoint small_faces a T b source).mpr ⟨cut, vertex⟩)
  · exact Or.inr ⟨u, v, edge,
      (graph.cut_edge_strips_iff_endpoint small_faces a T edge (strips u v edge) b source).mpr ⟨cut, inside⟩⟩

include graph small_faces in
/-- The finite tree and every strip family can be constructed simultaneously. -/
theorem exists_cut_tree_radial_partition (a : frontier P.body) :
    ∃ T : P.CutLocusTree a,
      ∃ strips : ∀ u v : T.vertices, ∀ edge : T.graph.Adj u v, CutEdgeStrips T edge,
        ∀ b : frontier P.body, b = a ∨ b ∈ P.cutSet a ∨ b ∈ T.vertexRays ∨
          ∃ u v : T.vertices, ∃ edge : T.graph.Adj u v,
            b ∈ routeStrip (strips u v edge).first ∪ routeStrip (strips u v edge).second := by
  classical
  obtain ⟨T⟩ := graph.exists_regular_cut_tree small_faces a
  let strips (u v : T.vertices) (edge : T.graph.Adj u v) : CutEdgeStrips T edge :=
    Classical.choice (graph.exists_cut_edge_strips small_faces a T edge)
  exact ⟨T, strips, graph.cut_tree_radial_partition small_faces a T strips⟩

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
