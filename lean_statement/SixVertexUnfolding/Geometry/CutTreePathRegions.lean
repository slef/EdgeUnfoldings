import SixVertexUnfolding.Geometry.ExpandingRegionChains

/-! The wedge update uses exactly the angle sum of the extended simple
path. Successive region steps therefore have matching outer-angle parameters. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Real Set Wedge

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4)
    {a : frontier P.body} (T : P.CutLocusTree a)
    [Fintype T.vertices] [DecidableRel T.graph.Adj]
    (models : (d : T.graph.Dart) → CutEdgeMetricModel T d.adj)

include small_faces in
/-- The actual path supplies a region step whose new angle is the next path sum.
The final theorem must still provide the full sequence of junction data. -/
theorem path_region_step (source : Fin 6)
    (at_source : (a : Space) = (graph.vertex source : Space))
    {u v : T.vertices} (path : T.graph.Walk u v) (simple : path.IsPath)
    (fan : JunctionFan T v)
    (incoming outgoing : circularGapMidpoints fan.order.angles fan.order.first fan.order.last)
    (distinct : incoming ≠ outgoing)
    (fresh : (fan.order.neighbors outgoing).val ∉ path.support)
    {next_chart : P.CutVoronoiChart a (T.vertexTarget (fan.order.neighbors outgoing).val)} {φ : ℝ}
    (next : IncidentTriangles T (fan.order.neighbors outgoing).property.symm next_chart φ) :
    Nonempty (RegionStep
      ((fan.triangles incoming).incomingWedge
        (π / 2 + ∑ d ∈ path.darts.toFinset, (models d).sourceAngle))
      (next.incomingWedge (π / 2 + ∑ d ∈
        (path.concat (fan.order.neighbors outgoing).property).darts.toFinset, (models d).sourceAngle))
      (fan.triangles outgoing).developedKite) := by
  obtain ⟨move⟩ := graph.path_wedge_move small_faces T models source at_source path simple fan
    incoming outgoing distinct fresh next
  have next_angle :
      π / 2 + (∑ d ∈ path.darts.toFinset, (models d).sourceAngle) +
          (fan.triangles outgoing).model.sourceAngle =
        π / 2 + ∑ d ∈ (path.concat (fan.order.neighbors outgoing).property).darts.toFinset,
          (models d).sourceAngle := by
    rw [path_extension_angle_sum T models path (fan.order.neighbors outgoing).property fresh]
    have same := (models ⟨(v, (fan.order.neighbors outgoing).val),
      (fan.order.neighbors outgoing).property⟩).same_edge_sourceAngle (fan.triangles outgoing).model
    rw [same]
    ring
  have step := move.toRegionStep
  rw [next_angle] at step
  exact ⟨step⟩

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
