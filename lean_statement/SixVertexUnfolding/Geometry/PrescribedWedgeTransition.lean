import SixVertexUnfolding.Geometry.ExpandingRegionChains

/-! The expanding-region step works with a previously chosen edge
transition. This lets every path use the same global surface placement. -/

namespace SixVertexUnfolding.ConvexPolyhedron.JunctionFan

open Real Set Wedge

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a}
    {u : T.vertices} (fan : JunctionFan T u)

/-- Prescribe the coordinate change first, then carry out the exact kite-addition step. -/
theorem region_step_with_motion
    (incoming outgoing : circularGapMidpoints fan.order.angles fan.order.first fan.order.last)
    (distinct : incoming ≠ outgoing)
    {next_chart : P.CutVoronoiChart a (T.vertexTarget (fan.order.neighbors outgoing).val)} {φ : ℝ}
    (next : IncidentTriangles T (fan.order.neighbors outgoing).property.symm next_chart φ)
    (ω : ℝ) (outer_lower : π / 2 ≤ ω)
    (budget : ω + (fan.triangles outgoing).model.sourceAngle ≤ 3 * π / 2)
    (motion : Plane ≃ᵃⁱ[ℝ] Plane)
    (old_root : motion fan.order.chart.origin = next_chart.origin +
      dist ((fan.order.neighbors outgoing).val : Space) (u : Space) • direction φ)
    (next_root : motion (fan.order.chart.origin +
      dist (u : Space) ((fan.order.neighbors outgoing).val : Space) • direction outgoing) = next_chart.origin) :
    ∃ step : RegionStep ((fan.triangles incoming).incomingWedge ω)
      (next.incomingWedge (ω + (fan.triangles outgoing).model.sourceAngle))
      (fan.triangles outgoing).developedKite, step.motion = motion := by
  obtain ⟨α, β, γ, δ, incoming_gap, outgoing_gap, incoming_midpoint, outgoing_midpoint,
    radius, Θ, _, _, _, radius_eq, corner_eq, contained, disjoint, returned⟩ :=
    fan.wedge_step_with_parameters incoming outgoing distinct ω outer_lower budget
  have image := (fan.triangles outgoing).next_wedge_image next motion old_root next_root
    radius_eq corner_eq (ω + (fan.triangles outgoing).model.sourceAngle)
  have image' : motion '' {x | x - (fan.order.chart.origin +
      dist (u : Space) ((fan.order.neighbors outgoing).val : Space) • direction outgoing) ∈
        polarRegion radius (ω + (fan.triangles outgoing).model.sourceAngle)
          (Θ + (γ + δ) / 2) (2 * π - Θ + (γ + δ) / 2)} =
      next.incomingWedge (ω + (fan.triangles outgoing).model.sourceAngle) := by
    simpa only [outgoing_midpoint] using image
  rw [returned] at image'
  have kite := fan.developed_kite_eq outgoing outgoing_gap outgoing_midpoint
  rw [← kite] at disjoint image'
  refine ⟨{
    enlarged := {x | x - fan.order.chart.origin ∈
      polarRegion (P.surfaceDist a (T.vertexTarget u)) ω δ (γ + 2 * π)}
    motion := motion
    contains := ?_
    avoids := disjoint
    updated := image' }, rfl⟩
  rw [fan.incoming_wedge_eq incoming incoming_gap incoming_midpoint]
  exact contained

end SixVertexUnfolding.ConvexPolyhedron.JunctionFan
