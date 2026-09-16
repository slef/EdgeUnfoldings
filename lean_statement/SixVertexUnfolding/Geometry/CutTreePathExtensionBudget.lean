import SixVertexUnfolding.Geometry.CutTreePathBudget
import SixVertexUnfolding.Geometry.JunctionWedgeStep

/-! Extending a simple path supplies the precise angle inequality for
the next actual junction wedge step. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set Real

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4)
    {a : frontier P.body} (T : P.CutLocusTree a)
    [Fintype T.vertices] [DecidableRel T.graph.Adj]
    (models : (d : T.graph.Dart) → CutEdgeMetricModel T d.adj)

omit [Fintype T.vertices] [DecidableRel T.graph.Adj] in
/-- The exact new source-angle sum, before applying the curvature bound. -/
theorem path_extension_angle_sum {u v w : T.vertices} (path : T.graph.Walk u v)
    (edge : T.graph.Adj v w) (fresh : w ∉ path.support) :
    (∑ d ∈ (path.concat edge).darts.toFinset, (models d).sourceAngle) =
      (∑ d ∈ path.darts.toFinset, (models d).sourceAngle) +
        (models ⟨(v, w), edge⟩).sourceAngle := by
  classical
  let next : T.graph.Dart := ⟨(v, w), edge⟩
  have new_edge : next ∉ path.darts.toFinset := by
    intro member
    exact fresh (path.dart_snd_mem_support_of_mem_darts (List.mem_toFinset.mp member))
  have sum_extended : (∑ d ∈ (path.concat edge).darts.toFinset, (models d).sourceAngle) =
      (∑ d ∈ path.darts.toFinset, (models d).sourceAngle) + (models next).sourceAngle := by
    have finset : (path.darts.concat next).toFinset = insert next path.darts.toFinset := by
      ext d
      simp [List.concat_eq_append]
    rw [SimpleGraph.Walk.darts_concat]
    change (∑ d ∈ (path.darts.concat next).toFinset, (models d).sourceAngle) = _
    rw [finset, Finset.sum_insert new_edge]
    exact add_comm _ _
  exact sum_extended

include small_faces in
/-- The angle added by the next edge fits the remaining outer-angle budget. -/
theorem path_extension_angle_budget (source : Fin 6)
    (at_source : (a : Space) = (graph.vertex source : Space))
    {u v w : T.vertices} (path : T.graph.Walk u v) (simple : path.IsPath)
    (edge : T.graph.Adj v w) (fresh : w ∉ path.support) :
    π / 2 + (∑ d ∈ path.darts.toFinset, (models d).sourceAngle) +
      (models ⟨(v, w), edge⟩).sourceAngle < 3 * π / 2 := by
  have sum_extended := path_extension_angle_sum T models path edge fresh
  have bounded := graph.path_source_angle_sum_lt_pi small_faces T models source at_source
    (path.concat edge) (simple.concat fresh edge)
  rw [sum_extended] at bounded
  linarith

include small_faces in
/-- Use the actual outgoing fan triangle, even if its coordinates were chosen independently. -/
theorem junction_path_angle_budget (source : Fin 6)
    (at_source : (a : Space) = (graph.vertex source : Space))
    {u v : T.vertices} (path : T.graph.Walk u v) (simple : path.IsPath)
    (fan : JunctionFan T v)
    (outgoing : circularGapMidpoints fan.order.angles fan.order.first fan.order.last)
    (fresh : (fan.order.neighbors outgoing).val ∉ path.support) :
    π / 2 ≤ π / 2 + (∑ d ∈ path.darts.toFinset, (models d).sourceAngle) ∧
      π / 2 + (∑ d ∈ path.darts.toFinset, (models d).sourceAngle) +
        (fan.triangles outgoing).model.sourceAngle < 3 * π / 2 := by
  have edge := (fan.order.neighbors outgoing).property
  have bounded := graph.path_extension_angle_budget small_faces T models source at_source path simple edge fresh
  have same := (models ⟨(v, (fan.order.neighbors outgoing).val), edge⟩).same_edge_sourceAngle
    (fan.triangles outgoing).model
  rw [same] at bounded
  exact ⟨(graph.path_outer_angle_bounds small_faces T models source at_source path simple).1, bounded⟩

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
