import SixVertexUnfolding.Geometry.InitialKiteWedge
import SixVertexUnfolding.Geometry.JunctionIncomingWedges
import SixVertexUnfolding.Geometry.JunctionWedgeStep

/-! The final exclusion step needs no chart at the next endpoint.
It also separates complete incident kites, including those ending at vertices. -/

namespace SixVertexUnfolding.ConvexPolyhedron.JunctionFan

open Real Set Wedge

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a}
    {u : T.vertices} (fan : JunctionFan T u)

/-- Exclude the next actual kite without moving to a chart at its far endpoint. -/
theorem incoming_wedge_avoids_kite
    (incoming outgoing : circularGapMidpoints fan.order.angles fan.order.first fan.order.last)
    (distinct : incoming ≠ outgoing) (ω : ℝ) (outer_lower : π / 2 ≤ ω)
    (budget : ω + (fan.triangles outgoing).model.sourceAngle ≤ 3 * π / 2) :
    Disjoint ((fan.triangles incoming).incomingWedge ω)
      (interior (fan.triangles outgoing).developedKite) := by
  obtain ⟨α, β, γ, δ, ig, og, im, om, _, _, _, _, _, contains, avoids, _⟩ :=
    fan.wedge_step incoming outgoing distinct ω outer_lower budget
  rw [← fan.incoming_wedge_eq incoming ig im] at contains
  rw [← fan.developed_kite_eq outgoing og om] at avoids
  exact avoids.mono contains Subset.rfl

/-- Two whole incident kites are separate whenever their two source angles fit the budget. -/
theorem incident_kites_nonoverlap
    (incoming outgoing : circularGapMidpoints fan.order.angles fan.order.first fan.order.last)
    (distinct : incoming ≠ outgoing)
    (budget : (fan.triangles incoming).model.sourceAngle +
      (fan.triangles outgoing).model.sourceAngle ≤ π) :
    Disjoint (fan.triangles incoming).developedKite
      (interior (fan.triangles outgoing).developedKite) := by
  have avoids := fan.incoming_wedge_avoids_kite incoming outgoing distinct
    (π / 2 + (fan.triangles incoming).model.sourceAngle)
    (by linarith [(fan.triangles incoming).model.sourceAngle_pos]) (by linarith)
  exact avoids.mono (fan.triangles incoming).initial_kite_in_wedge Subset.rfl

end SixVertexUnfolding.ConvexPolyhedron.JunctionFan
