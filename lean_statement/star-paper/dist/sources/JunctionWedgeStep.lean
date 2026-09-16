import SixVertexUnfolding.Geometry.JunctionFan
import SixVertexUnfolding.Geometry.JunctionGapAngles
import SixVertexUnfolding.Geometry.GapKiteStep
import SixVertexUnfolding.Geometry.NextWedgeParameters

/-! The actual ordered fan supplies the geometric premises of a wedge step.
Only the cumulative source-angle budget remains a premise for the global
argument. No independent arm-order or coordinate assumptions are required.
-/

namespace SixVertexUnfolding.ConvexPolyhedron.JunctionFan

open Real Set EuclideanGeometry Wedge

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a}
  {u : T.vertices} (fan : JunctionFan T u)

/-- Move through any chosen outgoing edge after entering along a different
incident edge. The angle increment is the actual metric kite's source angle. -/
theorem wedge_step_with_parameters
    (incoming outgoing : circularGapMidpoints fan.order.angles fan.order.first fan.order.last)
    (distinct : incoming ≠ outgoing) (ω : ℝ) (outer_lower : π / 2 ≤ ω)
    (budget : ω + (fan.triangles outgoing).model.sourceAngle ≤ 3 * π / 2) :
    let z := fan.order.chart.origin
    let d := P.surfaceDist a (T.vertexTarget u)
    let L := dist (u : Space) ((fan.order.neighbors outgoing).val : Space)
    let y := z + L • direction outgoing
    ∃ α β γ δ : ℝ,
      IsCircularGap fan.order.angles fan.order.first fan.order.last α β ∧
      IsCircularGap fan.order.angles fan.order.first fan.order.last γ δ ∧
      (incoming : ℝ) = (α + β) / 2 ∧ (outgoing : ℝ) = (γ + δ) / 2 ∧
      ∃ D Θ : ℝ, 0 < D ∧ 0 < Θ ∧ Θ < π ∧
        D = P.surfaceDist a (T.vertexTarget (fan.order.neighbors outgoing).val) ∧
        π - Θ = angle (fan.triangles outgoing).model.first
          (fan.triangles outgoing).model.right (fan.triangles outgoing).model.left ∧
        let W := {x | x - z ∈ polarRegion d ω α β}
        let V := {x | x - z ∈ polarRegion d ω δ (γ + 2 * π)}
        let W' := {x | x - y ∈ polarRegion D (ω + (fan.triangles outgoing).model.sourceAngle)
          (Θ + (γ + δ) / 2) (2 * π - Θ + (γ + δ) / 2)}
        W ⊆ V ∧ Disjoint V (interior (gapKite z d L γ δ)) ∧ W' = V ∪ gapKite z d L γ δ := by
  dsimp only
  obtain ⟨α, β, incoming_gap, incoming_midpoint⟩ :=
    (mem_circularGapMidpoints_iff fan.order.angles fan.order.first fan.order.last incoming).mp incoming.property
  obtain ⟨γ, δ, outgoing_gap, outgoing_midpoint⟩ :=
    (mem_circularGapMidpoints_iff fan.order.angles fan.order.first fan.order.last outgoing).mp outgoing.property
  have midpoint_distinct : (α + β) / 2 ≠ (γ + δ) / 2 := by
    intro equal
    exact distinct (Subtype.ext (incoming_midpoint.trans (equal.trans outgoing_midpoint.symm)))
  have separated : (β ≤ γ ∧ δ ≤ α + 2 * π) ∨ (δ ≤ α ∧ β ≤ γ + 2 * π) := by
    rcases lt_or_gt_of_ne midpoint_distinct with before | after
    · exact Or.inl (circular_gaps_separated fan.order.angles fan.order.increasing fan.order.bounds
        fan.order.first fan.order.last fan.order.at_first fan.order.at_last incoming_gap outgoing_gap before)
    · exact Or.inr (circular_gaps_separated fan.order.angles fan.order.increasing fan.order.bounds
        fan.order.first fan.order.last fan.order.at_first fan.order.at_last outgoing_gap incoming_gap after)
  obtain ⟨ordered, width, _, _, first_source, second_source, empty_gap⟩ := circular_gap_spec
    fan.order.sites fan.order.angles fan.order.increasing fan.order.bounds fan.order.chart.origin
    (P.surfaceDist a (T.vertexTarget u)) fan.order.position fan.order.first fan.order.last
    fan.order.at_first fan.order.at_last fan.order.two outgoing_gap
  have on_ray (ρ : ℝ) (hr : ρ ∈ Ioo (0 : ℝ) fan.order.radius) :
      fan.order.chart.map (fan.order.chart.origin + ρ • direction ((γ + δ) / 2)) ∈
        openSegment ℝ (T.vertexTarget u : Space) ((fan.order.neighbors outgoing).val : Space) := by
    rw [← outgoing_midpoint]
    exact fan.order.rays outgoing ρ hr
  have source_positive : 0 < P.surfaceDist a (T.vertexTarget u) := by
    simpa using CutVoronoiChart.tail_radius_pos (T.vertexTarget_different u) (0 : unitInterval)
      (by change (0 : ℝ) < 1; norm_num)
  have length_positive : 0 < dist (u : Space) ((fan.order.neighbors outgoing).val : Space) := by
    apply dist_pos.mpr
    intro same
    exact (fan.order.neighbors outgoing).property.ne (Subtype.ext same)
  have angle_eq := fan.order.chart.incident_gap_source_angle T (fan.order.neighbors outgoing).property
    rfl (fan.triangles outgoing).model ordered width first_source second_source empty_gap
    fan.order.radius_positive on_ray
  change angle fan.order.chart.origin
    (fan.order.chart.origin + P.surfaceDist a (T.vertexTarget u) • direction δ)
    (fan.order.chart.origin + dist (u : Space) ((fan.order.neighbors outgoing).val : Space) •
      direction ((γ + δ) / 2)) = (fan.triangles outgoing).model.sourceAngle at angle_eq
  have step := gap_rotate_and_move_with_sources fan.order.chart.origin source_positive length_positive
    ordered width separated outer_lower (by rw [angle_eq]; exact budget)
  dsimp only at step
  rw [angle_eq] at step
  obtain ⟨D, Θ, dp, tp, ts, source_position, _, step⟩ := step
  have parameters := fan.order.chart.next_wedge_parameters T (fan.order.neighbors outgoing).property
    rfl (fan.triangles outgoing).model ordered width first_source second_source empty_gap
    fan.order.radius_positive on_ray dp tp ts source_position
  refine ⟨α, β, γ, δ, incoming_gap, outgoing_gap, incoming_midpoint, outgoing_midpoint,
    D, Θ, dp, tp, ts, parameters.1, parameters.2, ?_⟩
  simpa only [outgoing_midpoint] using step


/-- The set-theoretic form of the step, with its identified parameters omitted. -/
theorem wedge_step
    (incoming outgoing : circularGapMidpoints fan.order.angles fan.order.first fan.order.last)
    (distinct : incoming ≠ outgoing) (ω : ℝ) (outer_lower : π / 2 ≤ ω)
    (budget : ω + (fan.triangles outgoing).model.sourceAngle ≤ 3 * π / 2) :
    let z := fan.order.chart.origin
    let d := P.surfaceDist a (T.vertexTarget u)
    let L := dist (u : Space) ((fan.order.neighbors outgoing).val : Space)
    let y := z + L • direction outgoing
    ∃ α β γ δ : ℝ,
      IsCircularGap fan.order.angles fan.order.first fan.order.last α β ∧
      IsCircularGap fan.order.angles fan.order.first fan.order.last γ δ ∧
      (incoming : ℝ) = (α + β) / 2 ∧ (outgoing : ℝ) = (γ + δ) / 2 ∧
      ∃ D Θ : ℝ, 0 < D ∧ 0 < Θ ∧ Θ < π ∧
        let W := {x | x - z ∈ polarRegion d ω α β}
        let V := {x | x - z ∈ polarRegion d ω δ (γ + 2 * π)}
        let W' := {x | x - y ∈ polarRegion D (ω + (fan.triangles outgoing).model.sourceAngle)
          (Θ + (γ + δ) / 2) (2 * π - Θ + (γ + δ) / 2)}
        W ⊆ V ∧ Disjoint V (interior (gapKite z d L γ δ)) ∧ W' = V ∪ gapKite z d L γ δ := by
  obtain ⟨α, β, γ, δ, ig, og, im, om, D, Θ, dp, tp, ts, _, _, step⟩ :=
    fan.wedge_step_with_parameters incoming outgoing distinct ω outer_lower budget
  exact ⟨α, β, γ, δ, ig, og, im, om, D, Θ, dp, tp, ts, step⟩

end SixVertexUnfolding.ConvexPolyhedron.JunctionFan
