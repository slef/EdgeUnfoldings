import SixVertexUnfolding.Geometry.CutTreeCharts
import SixVertexUnfolding.Geometry.SmallPolyhedronJunctionFan
import SixVertexUnfolding.Geometry.SmallPolyhedronCutTreeTriangleCoverage
import SixVertexUnfolding.Geometry.SmallPolyhedronUniqueRouteLeaves

/-! Actual radial triangle charts for small polyhedra with a cofacial source.
The construction proves surface coverage, flat junction compatibility,
original-vertex leaves, and consistent frames across every tree edge.
It precedes the separate source-angle budget and global nonoverlap proof. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

variable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include size small_faces in
/-- For a cofacial source, construct the entire chart collection and its common frames. -/
theorem small_exists_cut_tree_charts (a : frontier P.body) (T : P.CutLocusTree a)
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val) :
    Nonempty (CutTreeCharts T) := by
  classical
  let fan (u : T.vertices) (nonvertex : (u : Space) ∉ P.vertices) :=
    Classical.choice (small_exists_junction_fan size small_faces a T u nonvertex)
  let triangles {u v : T.vertices} (edge : T.graph.Adj u v) : PlacedCutEdgeTriangles T edge :=
    if original : (u : Space) ∈ P.vertices then
      ⟨Classical.choice (small_exists_cut_edge_triangles size small_faces a T edge), AffineIsometryEquiv.refl ℝ Plane⟩
    else ((fan u original).edgeTriangles edge).placed
  obtain ⟨frames⟩ := exists_cut_tree_frames T @triangles
  refine ⟨{
    fan := fan
    triangles := @triangles
    at_fan := ?_
    original_leaves := fun u original =>
      small_cofacial_source_original_is_leaf size small_faces a T cofacial u original
    frames := frames
    covers := ?_ }⟩
  · intro u v edge nonvertex
    simp only [triangles, dif_neg nonvertex]
  · intro b
    obtain ⟨d, member⟩ := small_cut_tree_triangles_cover size small_faces a T
      (fun d => (triangles d.adj).toCutEdgeTriangles) b
    exact ⟨d.fst, d.snd, d.adj, member⟩

include size small_faces in
/-- A universal source supplies all the geometric charts of the star construction. -/
theorem small_universal_source_cut_tree_charts
    (a : frontier P.body) (source : P.Vertex) (at_source : (a : Space) = (source : Space))
    (universal : ∀ v : P.Vertex, v ≠ source → P.edgeGraph.Adj source v)
    (T : P.CutLocusTree a) : Nonempty (CutTreeCharts T) :=
  small_exists_cut_tree_charts size small_faces a T
    (universal_source_cofacial a source at_source universal)

include size small_faces in
/-- Construct both the actual cut tree and its complete chart collection at a universal source. -/
theorem small_exists_universal_star_charts
    (a : frontier P.body) (source : P.Vertex) (at_source : (a : Space) = (source : Space))
    (universal : ∀ v : P.Vertex, v ≠ source → P.edgeGraph.Adj source v) :
    ∃ T : P.CutLocusTree a, Nonempty (CutTreeCharts T) := by
  obtain ⟨T⟩ := small_exists_regular_cut_tree size small_faces a
  exact ⟨T, small_universal_source_cut_tree_charts size small_faces a source at_source universal T⟩

end SixVertexUnfolding.ConvexPolyhedron
