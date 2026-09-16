import SixVertexUnfolding.Geometry.JunctionEdgeIndices
import SixVertexUnfolding.Geometry.CutTreePathRegions

/-! Supply the complete step from two successive actual junction fans.
The caller names tree edges, not gap indices or numerical angle premises. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Real Set Wedge

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4)
    {a : frontier P.body} (T : P.CutLocusTree a)
    [Fintype T.vertices] [DecidableRel T.graph.Adj]
    (models : (d : T.graph.Dart) → CutEdgeMetricModel T d.adj)

include small_faces in
/-- Two actual fans and an extended simple path determine a valid region step. -/
theorem edge_path_region_step (source : Fin 6)
    (at_source : (a : Space) = (graph.vertex source : Space))
    {start previous u v : T.vertices} (path : T.graph.Walk start u) (simple : path.IsPath)
    (fan : JunctionFan T u) (next : JunctionFan T v)
    (incoming : T.graph.Adj u previous) (outgoing : T.graph.Adj u v)
    (distinct : previous ≠ v) (fresh : v ∉ path.support) :
    Nonempty (RegionStep
      ((fan.edgeTriangles incoming).incomingWedge
        (π / 2 + ∑ d ∈ path.darts.toFinset, (models d).sourceAngle))
      ((next.edgeTriangles outgoing.symm).incomingWedge
        (π / 2 + ∑ d ∈ (path.concat outgoing).darts.toFinset, (models d).sourceAngle))
      (fan.edgeTriangles outgoing).developedKite) := by
  have different : fan.edgeIndex incoming ≠ fan.edgeIndex outgoing := by
    intro same
    have neighbor := congrArg fan.order.neighbors same
    rw [fan.edgeIndex_neighbor, fan.edgeIndex_neighbor] at neighbor
    exact distinct (congrArg Subtype.val neighbor)
  have fresh_index : (fan.order.neighbors (fan.edgeIndex outgoing)).val ∉ path.support := by
    simpa only [fan.edgeIndex_neighbor] using fresh
  let wanted (w : {v : T.vertices // T.graph.Adj u v}) : Prop :=
    ∀ (next_chart : P.CutVoronoiChart a (T.vertexTarget w.val)) (φ : ℝ)
      (E : IncidentTriangles T w.property.symm next_chart φ),
      Nonempty (RegionStep
        ((fan.triangles (fan.edgeIndex incoming)).incomingWedge
          (π / 2 + ∑ d ∈ path.darts.toFinset, (models d).sourceAngle))
        (E.incomingWedge (π / 2 + ∑ d ∈ (path.concat w.property).darts.toFinset,
          (models d).sourceAngle))
        (fan.triangles (fan.edgeIndex outgoing)).developedKite)
  have available : wanted (fan.order.neighbors (fan.edgeIndex outgoing)) := by
    intro next_chart φ E
    exact graph.path_region_step small_faces T models source at_source path simple fan
      (fan.edgeIndex incoming) (fan.edgeIndex outgoing) different fresh_index E
  have actual : wanted ⟨v, outgoing⟩ :=
    Eq.mp (congrArg wanted (fan.edgeIndex_neighbor outgoing)) available
  rw [fan.edgeTriangles_wedge, fan.edgeTriangles_kite]
  exact actual next.order.chart (next.edgeIndex outgoing.symm) (next.edgeTriangles outgoing.symm)

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
