import SixVertexUnfolding.Geometry.CutTreePathExtensionBudget
import SixVertexUnfolding.Geometry.JunctionWedgeTransport
import SixVertexUnfolding.Geometry.JunctionDevelopedKites

/-! Construct the complete geometric step with its actual triangles.
Along a simple path from an original source, all angle premises are proved. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Real Set Wedge

namespace JunctionFan

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a}
    {u : T.vertices} (fan : JunctionFan T u)

/-- A proved step records the enlarged region and the same rigid motion
for its wedge and for its two actual triangle developments. -/
structure WedgeMove
    (incoming outgoing : circularGapMidpoints fan.order.angles fan.order.first fan.order.last)
    {next_chart : P.CutVoronoiChart a (T.vertexTarget (fan.order.neighbors outgoing).val)} {φ : ℝ}
    (next : IncidentTriangles T (fan.order.neighbors outgoing).property.symm next_chart φ)
    (ω : ℝ) where
  enlarged : Set Plane
  motion : Plane ≃ᵃⁱ[ℝ] Plane
  old_root : motion fan.order.chart.origin = next_chart.origin +
    dist (u : Space) ((fan.order.neighbors outgoing).val : Space) • direction φ
  next_root : motion (fan.order.chart.origin +
    dist (u : Space) ((fan.order.neighbors outgoing).val : Space) • direction outgoing) = next_chart.origin
  contains : (fan.triangles incoming).incomingWedge ω ⊆ enlarged
  avoids : Disjoint enlarged (interior (fan.triangles outgoing).developedKite)
  updated : motion '' (enlarged ∪ (fan.triangles outgoing).developedKite) =
    next.incomingWedge (ω + (fan.triangles outgoing).model.sourceAngle)
  agreement :
    (((fan.triangles outgoing).first_triangle.move (fan.triangles outgoing).motion).AgreesAfter
        (next.first_triangle.move next.motion) motion ∧
      ((fan.triangles outgoing).second_triangle.move (fan.triangles outgoing).motion).AgreesAfter
        (next.second_triangle.move next.motion) motion) ∨
    (((fan.triangles outgoing).first_triangle.move (fan.triangles outgoing).motion).AgreesAfter
        (next.second_triangle.move next.motion) motion ∧
      ((fan.triangles outgoing).second_triangle.move (fan.triangles outgoing).motion).AgreesAfter
        (next.first_triangle.move next.motion) motion)

/-- Construct every field from the actual ordered fan and the planar wedge theorem. -/
theorem exists_wedge_move
    (incoming outgoing : circularGapMidpoints fan.order.angles fan.order.first fan.order.last)
    (distinct : incoming ≠ outgoing)
    {next_chart : P.CutVoronoiChart a (T.vertexTarget (fan.order.neighbors outgoing).val)} {φ : ℝ}
    (next : IncidentTriangles T (fan.order.neighbors outgoing).property.symm next_chart φ)
    (ω : ℝ) (outer_lower : π / 2 ≤ ω)
    (budget : ω + (fan.triangles outgoing).model.sourceAngle ≤ 3 * π / 2) :
    Nonempty (fan.WedgeMove incoming outgoing next ω) := by
  obtain ⟨γ, δ, gap, midpoint, V, motion, old_root, next_root, contains, avoids, updated, agreement⟩ :=
    fan.wedge_step_across_edge incoming outgoing distinct next ω outer_lower budget
  rw [← fan.developed_kite_eq outgoing gap midpoint] at avoids updated
  exact ⟨⟨V, motion, old_root, next_root, contains, avoids, updated, agreement⟩⟩

end JunctionFan

namespace SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4)
    {a : frontier P.body} (T : P.CutLocusTree a)
    [Fintype T.vertices] [DecidableRel T.graph.Adj]
    (models : (d : T.graph.Dart) → CutEdgeMetricModel T d.adj)

include small_faces in
/-- A simple path supplies the angle budget for the complete next geometric step. -/
theorem path_wedge_move (source : Fin 6)
    (at_source : (a : Space) = (graph.vertex source : Space))
    {u v : T.vertices} (path : T.graph.Walk u v) (simple : path.IsPath)
    (fan : JunctionFan T v)
    (incoming outgoing : circularGapMidpoints fan.order.angles fan.order.first fan.order.last)
    (distinct : incoming ≠ outgoing)
    (fresh : (fan.order.neighbors outgoing).val ∉ path.support)
    {next_chart : P.CutVoronoiChart a (T.vertexTarget (fan.order.neighbors outgoing).val)} {φ : ℝ}
    (next : IncidentTriangles T (fan.order.neighbors outgoing).property.symm next_chart φ) :
    Nonempty (fan.WedgeMove incoming outgoing next
      (π / 2 + ∑ d ∈ path.darts.toFinset, (models d).sourceAngle)) := by
  obtain ⟨lower, budget⟩ := graph.junction_path_angle_budget small_faces T models source at_source
    path simple fan outgoing fresh
  exact fan.exists_wedge_move incoming outgoing distinct next _ lower budget.le

end SixVertexGraph
end SixVertexUnfolding.ConvexPolyhedron
