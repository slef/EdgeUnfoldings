import SixVertexUnfolding.Geometry.JunctionChartPlacement

/-! Every placement in a fixed fan, including far along a retained
ray, is one of the actual placements in the global development. -/

namespace SixVertexUnfolding.ConvexPolyhedron.CutTreeCharts

open Set

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a} (charts : CutTreeCharts T)

theorem places_from_fan (u : T.vertices) (nonvertex : (u : Space) ∉ P.vertices)
    (m : circularGapMidpoints (charts.fan u nonvertex).order.angles
      (charts.fan u nonvertex).order.first (charts.fan u nonvertex).order.last)
    (b : frontier P.body) (x : Plane) (placed : ((charts.fan u nonvertex).triangles m).placed.Places b x) :
    ∃ v : T.vertices, ∃ edge : T.graph.Adj u v,
      (charts.global edge).Places b (charts.frames.frame u x) := by
  let fan := charts.fan u nonvertex
  let edge := (fan.order.neighbors m).property
  refine ⟨(fan.order.neighbors m).val, edge, ?_⟩
  apply ((charts.triangles edge).places_inFrame (charts.frames.frame u) b _).mpr
  rw [(charts.frames.frame u).symm_apply_apply, charts.at_fan edge nonvertex]
  exact fan.indexed_placement m b x placed

end SixVertexUnfolding.ConvexPolyhedron.CutTreeCharts
