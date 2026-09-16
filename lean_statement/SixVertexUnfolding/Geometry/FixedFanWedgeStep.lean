import SixVertexUnfolding.Geometry.PrescribedWedgeTransition
import SixVertexUnfolding.Geometry.JunctionEdgeIndices
import SixVertexUnfolding.Geometry.JunctionTerminalStep

/-! The prescribed-motion wedge step indexed by actual tree edges.
The caller keeps its original fan and transition choices throughout. -/

namespace SixVertexUnfolding.ConvexPolyhedron.JunctionFan

open Set Real Wedge

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a}
    {u : T.vertices} (fan : JunctionFan T u)

theorem edgeTriangles_sourceAngle {v : T.vertices} (edge : T.graph.Adj u v) :
    (fan.edgeTriangles edge).model.sourceAngle = (fan.triangles (fan.edgeIndex edge)).model.sourceAngle := by
  have reindex {v w : T.vertices} {e : T.graph.Adj u v} {f : T.graph.Adj u w}
      {θ : ℝ} (same : v = w) (data : IncidentTriangles T e fan.order.chart θ) :
      (cast (by cases same; rfl : IncidentTriangles T e fan.order.chart θ =
        IncidentTriangles T f fan.order.chart θ) data).model.sourceAngle = data.model.sourceAngle := by
    cases same
    rfl
  exact reindex (f := edge) (congrArg Subtype.val (fan.edgeIndex_neighbor edge))
    (fan.triangles (fan.edgeIndex edge))

/-- Fixed fans and a fixed transition supply the complete region step on actual incident edges. -/
theorem edge_region_step_with_motion {previous v : T.vertices}
    (incoming : T.graph.Adj u previous) (outgoing : T.graph.Adj u v) (distinct : previous ≠ v)
    (next : JunctionFan T v) (ω : ℝ) (lower : π / 2 ≤ ω)
    (budget : ω + (fan.edgeTriangles outgoing).model.sourceAngle ≤ 3 * π / 2)
    (motion : Plane ≃ᵃⁱ[ℝ] Plane)
    (old_root : motion fan.order.chart.origin = next.order.chart.origin +
      dist (v : Space) (u : Space) • direction (next.edgeIndex outgoing.symm))
    (next_root : motion (fan.order.chart.origin + dist (u : Space) (v : Space) •
      direction (fan.edgeIndex outgoing)) = next.order.chart.origin) :
    ∃ step : RegionStep ((fan.edgeTriangles incoming).incomingWedge ω)
      ((next.edgeTriangles outgoing.symm).incomingWedge (ω + (fan.edgeTriangles outgoing).model.sourceAngle))
      (fan.edgeTriangles outgoing).developedKite, step.motion = motion := by
  have different : fan.edgeIndex incoming ≠ fan.edgeIndex outgoing := by
    intro same
    have neighbor := congrArg fan.order.neighbors same
    rw [fan.edgeIndex_neighbor, fan.edgeIndex_neighbor] at neighbor
    exact distinct (congrArg Subtype.val neighbor)
  have index_budget : ω + (fan.triangles (fan.edgeIndex outgoing)).model.sourceAngle ≤ 3 * π / 2 := by
    simpa only [fan.edgeTriangles_sourceAngle] using budget
  let wanted (w : {v : T.vertices // T.graph.Adj u v}) : Prop :=
    ∀ (chart : P.CutVoronoiChart a (T.vertexTarget w.val)) (φ : ℝ)
      (E : IncidentTriangles T w.property.symm chart φ),
      motion fan.order.chart.origin = chart.origin + dist (w.val : Space) (u : Space) • direction φ →
      motion (fan.order.chart.origin + dist (u : Space) (w.val : Space) •
        direction (fan.edgeIndex outgoing)) = chart.origin →
      ∃ step : RegionStep ((fan.triangles (fan.edgeIndex incoming)).incomingWedge ω)
        (E.incomingWedge (ω + (fan.triangles (fan.edgeIndex outgoing)).model.sourceAngle))
        (fan.triangles (fan.edgeIndex outgoing)).developedKite, step.motion = motion
  have available : wanted (fan.order.neighbors (fan.edgeIndex outgoing)) := by
    intro chart φ E old_root next_root
    exact fan.region_step_with_motion (fan.edgeIndex incoming) (fan.edgeIndex outgoing)
      different E ω lower index_budget motion old_root next_root
  have actual : wanted ⟨v, outgoing⟩ :=
    Eq.mp (congrArg wanted (fan.edgeIndex_neighbor outgoing)) available
  rw [fan.edgeTriangles_wedge, fan.edgeTriangles_kite, fan.edgeTriangles_sourceAngle]
  exact actual next.order.chart (next.edgeIndex outgoing.symm) (next.edgeTriangles outgoing.symm)
    old_root next_root

/-- The final exclusion also uses the actual named incident edges. -/
theorem edge_wedge_avoids_kite {previous v : T.vertices}
    (incoming : T.graph.Adj u previous) (outgoing : T.graph.Adj u v) (distinct : previous ≠ v)
    (ω : ℝ) (lower : π / 2 ≤ ω)
    (budget : ω + (fan.edgeTriangles outgoing).model.sourceAngle ≤ 3 * π / 2) :
    Disjoint ((fan.edgeTriangles incoming).incomingWedge ω)
      (interior (fan.edgeTriangles outgoing).developedKite) := by
  have different : fan.edgeIndex incoming ≠ fan.edgeIndex outgoing := by
    intro same
    have neighbor := congrArg fan.order.neighbors same
    rw [fan.edgeIndex_neighbor, fan.edgeIndex_neighbor] at neighbor
    exact distinct (congrArg Subtype.val neighbor)
  rw [fan.edgeTriangles_wedge, fan.edgeTriangles_kite]
  apply fan.incoming_wedge_avoids_kite _ _ different ω lower
  simpa only [fan.edgeTriangles_sourceAngle] using budget

end SixVertexUnfolding.ConvexPolyhedron.JunctionFan
