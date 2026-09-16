import SixVertexUnfolding.Geometry.JunctionChartPlacement
import SixVertexUnfolding.Geometry.SmallPolyhedronStarDevelopmentMap

/-! Transfer the actual junction disk to the one global development frame.
This version uses the broader small-polyhedron route results. Where
nonoverlap is needed, it is stated explicitly as separation of the charts. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set Filter Topology

variable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include size small_faces in
/-- The assembled development has the genuine flat-chart coordinates on each retained fan point. -/
theorem small_develop_fan_chart {a : frontier P.body} {T : P.CutLocusTree a} (charts : CutTreeCharts T)
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val)
    (u : T.vertices) (nonvertex : (u : Space) ∉ P.vertices)
    (x : Plane) (placed : (charts.fan u nonvertex).chartPlaces x)
    (b : P.UncutSurface a) (located : (b.val : Space) = (charts.fan u nonvertex).order.chart.map x) :
    charts.develop b.val = charts.frames.frame u x := by
  obtain ⟨inside, v, edge, actual⟩ := charts.fan_chart_placement u nonvertex x placed
  have same : (⟨(charts.fan u nonvertex).order.chart.map x,
      (charts.fan u nonvertex).order.chart.on_surface inside⟩ : frontier P.body) = b.val :=
    Subtype.ext located.symm
  exact small_develop_agrees size small_faces charts cofacial edge b.property (same ▸ actual)

end SixVertexUnfolding.ConvexPolyhedron
