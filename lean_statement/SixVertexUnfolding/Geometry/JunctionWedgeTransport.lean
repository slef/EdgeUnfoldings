import SixVertexUnfolding.Geometry.JunctionIncomingWedges
import SixVertexUnfolding.Geometry.JunctionWedgeStep

/-! One actual junction step, including the change of chart at the next
endpoint. The same transition carries the wedge and both whole triangles. -/

namespace SixVertexUnfolding.ConvexPolyhedron.JunctionFan

open Real Set Wedge

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a}
    {u : T.vertices} (fan : JunctionFan T u)

/-- Enlarge the incoming wedge, add the actual outgoing kite, and move
to the next junction. The angle budget is the only numerical premise. -/
theorem wedge_step_across_edge
    (incoming outgoing : circularGapMidpoints fan.order.angles fan.order.first fan.order.last)
    (distinct : incoming ≠ outgoing)
    {next_chart : P.CutVoronoiChart a (T.vertexTarget (fan.order.neighbors outgoing).val)}
    {φ : ℝ}
    (next : IncidentTriangles T (fan.order.neighbors outgoing).property.symm next_chart φ)
    (ω : ℝ) (outer_lower : π / 2 ≤ ω)
    (budget : ω + (fan.triangles outgoing).model.sourceAngle ≤ 3 * π / 2) :
    let z := fan.order.chart.origin
    let d := P.surfaceDist a (T.vertexTarget u)
    let L := dist (u : Space) ((fan.order.neighbors outgoing).val : Space)
    let D := fan.triangles outgoing
    ∃ γ δ : ℝ, IsCircularGap fan.order.angles fan.order.first fan.order.last γ δ ∧
      (outgoing : ℝ) = (γ + δ) / 2 ∧
      ∃ V : Set Plane, ∃ motion : Plane ≃ᵃⁱ[ℝ] Plane,
        motion z = next_chart.origin + L • direction φ ∧
        motion (z + L • direction outgoing) = next_chart.origin ∧
        (fan.triangles incoming).incomingWedge ω ⊆ V ∧
        Disjoint V (interior (gapKite z d L γ δ)) ∧
        motion '' (V ∪ gapKite z d L γ δ) = next.incomingWedge (ω + D.model.sourceAngle) ∧
        (((D.first_triangle.move D.motion).AgreesAfter
            (next.first_triangle.move next.motion) motion ∧
          (D.second_triangle.move D.motion).AgreesAfter
            (next.second_triangle.move next.motion) motion) ∨
         ((D.first_triangle.move D.motion).AgreesAfter
            (next.second_triangle.move next.motion) motion ∧
          (D.second_triangle.move D.motion).AgreesAfter
            (next.first_triangle.move next.motion) motion)) := by
  dsimp only
  obtain ⟨α, β, γ, δ, incoming_gap, outgoing_gap, incoming_midpoint, outgoing_midpoint,
    radius, Θ, _, _, _, radius_eq, corner_eq, contained, disjoint, returned⟩ :=
    fan.wedge_step_with_parameters incoming outgoing distinct ω outer_lower budget
  obtain ⟨motion, old_root, next_root, agreement⟩ := (fan.triangles outgoing).exists_edge_transition next
  have image := (fan.triangles outgoing).next_wedge_image next motion old_root next_root
    radius_eq corner_eq (ω + (fan.triangles outgoing).model.sourceAngle)
  have image' : motion '' {x | x - (fan.order.chart.origin +
      dist (u : Space) ((fan.order.neighbors outgoing).val : Space) • direction outgoing) ∈
        polarRegion radius (ω + (fan.triangles outgoing).model.sourceAngle)
          (Θ + (γ + δ) / 2) (2 * π - Θ + (γ + δ) / 2)} =
      next.incomingWedge (ω + (fan.triangles outgoing).model.sourceAngle) := by
    simpa only [outgoing_midpoint] using image
  rw [returned] at image'
  refine ⟨γ, δ, outgoing_gap, outgoing_midpoint,
    {x | x - fan.order.chart.origin ∈ polarRegion (P.surfaceDist a (T.vertexTarget u))
      ω δ (γ + 2 * π)}, motion, ?_, next_root, ?_, disjoint, image', ?_⟩
  · simpa only [dist_comm ((fan.order.neighbors outgoing).val : Space) (u : Space)] using old_root
  · rw [fan.incoming_wedge_eq incoming incoming_gap incoming_midpoint]
    exact contained
  · rcases agreement with same | swapped
    · exact Or.inl ⟨same.1, same.2.1⟩
    · exact Or.inr ⟨swapped.1, swapped.2.1⟩

end SixVertexUnfolding.ConvexPolyhedron.JunctionFan
