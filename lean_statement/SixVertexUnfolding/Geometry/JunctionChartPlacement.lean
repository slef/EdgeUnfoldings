import SixVertexUnfolding.Geometry.JunctionChartDisk
import SixVertexUnfolding.Geometry.StarDevelopmentMap

/-! Transfer the actual junction disk to the one global development frame. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

namespace JunctionFan

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a}
    {u : T.vertices} (fan : JunctionFan T u)

/-- Edge reindexing retains the entire actual surface placement. -/
theorem edgeTriangles_places {v : T.vertices} (edge : T.graph.Adj u v)
    (b : frontier P.body) (x : Plane) :
    (fan.edgeTriangles edge).placed.Places b x ↔
      (fan.triangles (fan.edgeIndex edge)).placed.Places b x := by
  have reindex {v w : T.vertices} {e : T.graph.Adj u v} {f : T.graph.Adj u w}
      {θ : ℝ} (same : v = w) (data : IncidentTriangles T e fan.order.chart θ) :
      (cast (by cases same; rfl : IncidentTriangles T e fan.order.chart θ =
        IncidentTriangles T f fan.order.chart θ) data).placed.Places b x ↔ data.placed.Places b x := by
    cases same
    rfl
  exact reindex (f := edge) (congrArg Subtype.val (fan.edgeIndex_neighbor edge))
    (fan.triangles (fan.edgeIndex edge))

theorem indexed_placement
    (m : circularGapMidpoints fan.order.angles fan.order.first fan.order.last)
    (b : frontier P.body) (x : Plane) (placed : (fan.triangles m).placed.Places b x) :
    (fan.edgeTriangles (fan.order.neighbors m).property).placed.Places b x := by
  apply (fan.edgeTriangles_places (fan.order.neighbors m).property b x).mpr
  change (fan.triangles (fan.order.neighbors.symm (fan.order.neighbors m))).placed.Places b x
  rw [fan.order.neighbors.symm_apply_apply]
  exact placed

end JunctionFan

namespace CutTreeCharts

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a} (charts : CutTreeCharts T)

theorem fan_chart_placement (u : T.vertices) (nonvertex : (u : Space) ∉ P.vertices)
    (x : Plane) (placed : (charts.fan u nonvertex).chartPlaces x) :
    ∃ inside : x ∈ (charts.fan u nonvertex).order.chart.domain,
      ∃ v : T.vertices, ∃ edge : T.graph.Adj u v,
        (charts.global edge).Places
          ⟨(charts.fan u nonvertex).order.chart.map x, (charts.fan u nonvertex).order.chart.on_surface inside⟩
          (charts.frames.frame u x) := by
  let fan := charts.fan u nonvertex
  obtain ⟨inside, m, placed⟩ := placed
  let edge := (fan.order.neighbors m).property
  refine ⟨inside, (fan.order.neighbors m).val, edge, ?_⟩
  apply ((charts.triangles edge).places_inFrame (charts.frames.frame u) _ _).mpr
  rw [(charts.frames.frame u).symm_apply_apply, charts.at_fan edge nonvertex]
  exact fan.indexed_placement m _ x placed

end CutTreeCharts

namespace SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- The assembled development has the genuine flat-chart coordinates on each retained fan point. -/
theorem develop_fan_chart {a : frontier P.body} {T : P.CutLocusTree a} (charts : CutTreeCharts T)
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val)
    (u : T.vertices) (nonvertex : (u : Space) ∉ P.vertices)
    (x : Plane) (placed : (charts.fan u nonvertex).chartPlaces x)
    (b : P.UncutSurface a) (located : (b.val : Space) = (charts.fan u nonvertex).order.chart.map x) :
    charts.develop b.val = charts.frames.frame u x := by
  obtain ⟨inside, v, edge, actual⟩ := charts.fan_chart_placement u nonvertex x placed
  have same : (⟨(charts.fan u nonvertex).order.chart.map x,
      (charts.fan u nonvertex).order.chart.on_surface inside⟩ : frontier P.body) = b.val :=
    Subtype.ext located.symm
  exact graph.develop_agrees small_faces charts cofacial edge b.property (same ▸ actual)

end SixVertexGraph
end SixVertexUnfolding.ConvexPolyhedron
