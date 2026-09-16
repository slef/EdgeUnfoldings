import SixVertexUnfolding.Geometry.JunctionIncomingWedges
import SixVertexUnfolding.Geometry.JunctionDevelopedKites

/-! Select a junction's already constructed incident data by the actual
tree edge, so that path arguments need no angular-index choices. -/

namespace SixVertexUnfolding.ConvexPolyhedron.JunctionFan

open Set

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a}
    {u : T.vertices} (fan : JunctionFan T u)

/-- The unique gap ray belonging to a prescribed neighboring tree vertex. -/
noncomputable def edgeIndex {v : T.vertices} (edge : T.graph.Adj u v) :
    circularGapMidpoints fan.order.angles fan.order.first fan.order.last :=
  fan.order.neighbors.symm ⟨v, edge⟩

theorem edgeIndex_neighbor {v : T.vertices} (edge : T.graph.Adj u v) :
    fan.order.neighbors (fan.edgeIndex edge) = ⟨v, edge⟩ :=
  fan.order.neighbors.apply_symm_apply _

/-- Reindex the same two developments by their actual oriented edge. -/
noncomputable def edgeTriangles {v : T.vertices} (edge : T.graph.Adj u v) :
    IncidentTriangles T edge fan.order.chart (fan.edgeIndex edge) := by
  have data := fan.triangles (fan.edgeIndex edge)
  simpa only [edgeIndex_neighbor] using data

/-- Independent records in one chart with the same ray have the same incoming wedge. -/
theorem incoming_wedge_independent {v : T.vertices} (edge : T.graph.Adj u v)
    (other : IncidentTriangles T edge fan.order.chart (fan.edgeIndex edge)) (ω : ℝ) :
    other.incomingWedge ω = (fan.edgeTriangles edge).incomingWedge ω := by
  unfold IncidentTriangles.incomingWedge
  rw [(other.model.same_edge_corner_angles (fan.edgeTriangles edge).model).1]

/-- Reindexing retains the incoming region of the actual angular fan. -/
theorem edgeTriangles_wedge {v : T.vertices} (edge : T.graph.Adj u v) (ω : ℝ) :
    (fan.edgeTriangles edge).incomingWedge ω = (fan.triangles (fan.edgeIndex edge)).incomingWedge ω := by
  have reindex {v w : T.vertices} {e : T.graph.Adj u v} {f : T.graph.Adj u w}
      {θ : ℝ} (same : v = w) (data : IncidentTriangles T e fan.order.chart θ) :
      (cast (by cases same; rfl : IncidentTriangles T e fan.order.chart θ =
        IncidentTriangles T f fan.order.chart θ) data).incomingWedge ω = data.incomingWedge ω := by
    cases same
    rfl
  exact reindex (f := edge) (congrArg Subtype.val (fan.edgeIndex_neighbor edge))
    (fan.triangles (fan.edgeIndex edge))

/-- Reindexing also retains the two complete triangle images. -/
theorem edgeTriangles_kite {v : T.vertices} (edge : T.graph.Adj u v) :
    (fan.edgeTriangles edge).developedKite = (fan.triangles (fan.edgeIndex edge)).developedKite := by
  have reindex {v w : T.vertices} {e : T.graph.Adj u v} {f : T.graph.Adj u w}
      {θ : ℝ} (same : v = w) (data : IncidentTriangles T e fan.order.chart θ) :
      (cast (by cases same; rfl : IncidentTriangles T e fan.order.chart θ =
        IncidentTriangles T f fan.order.chart θ) data).developedKite = data.developedKite := by
    cases same
    rfl
  exact reindex (f := edge) (congrArg Subtype.val (fan.edgeIndex_neighbor edge))
    (fan.triangles (fan.edgeIndex edge))

end SixVertexUnfolding.ConvexPolyhedron.JunctionFan
