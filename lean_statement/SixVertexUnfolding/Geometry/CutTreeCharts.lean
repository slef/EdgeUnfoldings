import SixVertexUnfolding.Geometry.CutTreeFrames
import SixVertexUnfolding.Geometry.UniqueRouteLeaves
import SixVertexUnfolding.Geometry.JunctionEdgeIndices
import SixVertexUnfolding.Geometry.CutTreeTriangleCoverage

/-! Choose all actual radial triangle charts simultaneously. Internal
vertices use their proved flat fans, original vertices are leaves, and
one set of frames aligns every reverse-edge pair throughout the tree.
This still precedes the proof of global nonoverlap and the cut-surface gluing. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- Actual local charts with coherent global frames and full surface coverage. -/
structure CutTreeCharts {P : ConvexPolyhedron} {a : frontier P.body} (T : P.CutLocusTree a) where
  fan : ∀ u : T.vertices, (u : Space) ∉ P.vertices → JunctionFan T u
  triangles : ∀ {u v : T.vertices} (edge : T.graph.Adj u v), PlacedCutEdgeTriangles T edge
  at_fan : ∀ {u v : T.vertices} (edge : T.graph.Adj u v) (nonvertex : (u : Space) ∉ P.vertices),
    triangles edge = ((fan u nonvertex).edgeTriangles edge).placed
  original_leaves : ∀ u : T.vertices, (u : Space) ∈ P.vertices → ∃! v, T.graph.Adj u v
  frames : CutTreeFrames T triangles
  covers : ∀ b : frontier P.body, ∃ u v : T.vertices, ∃ edge : T.graph.Adj u v,
    b ∈ (triangles edge).region

namespace SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- For a cofacial source, construct the entire chart collection and its common frames. -/
theorem exists_cut_tree_charts (a : frontier P.body) (T : P.CutLocusTree a)
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val) :
    Nonempty (CutTreeCharts T) := by
  classical
  let fan (u : T.vertices) (nonvertex : (u : Space) ∉ P.vertices) :=
    Classical.choice (graph.exists_junction_fan small_faces a T u nonvertex)
  let triangles {u v : T.vertices} (edge : T.graph.Adj u v) : PlacedCutEdgeTriangles T edge :=
    if original : (u : Space) ∈ P.vertices then
      ⟨Classical.choice (graph.exists_cut_edge_triangles small_faces a T edge), AffineIsometryEquiv.refl ℝ Plane⟩
    else ((fan u original).edgeTriangles edge).placed
  obtain ⟨frames⟩ := exists_cut_tree_frames T @triangles
  refine ⟨{
    fan := fan
    triangles := @triangles
    at_fan := ?_
    original_leaves := fun u original =>
      (graph.cofacial_source_leaf_iff_original small_faces a T cofacial u).mpr original
    frames := frames
    covers := ?_ }⟩
  · intro u v edge nonvertex
    simp only [triangles, dif_neg nonvertex]
  · intro b
    obtain ⟨d, member⟩ := graph.cut_tree_triangles_cover small_faces a T
      (fun d => (triangles d.adj).toCutEdgeTriangles) b
    exact ⟨d.fst, d.snd, d.adj, member⟩

end SixVertexGraph
end SixVertexUnfolding.ConvexPolyhedron
