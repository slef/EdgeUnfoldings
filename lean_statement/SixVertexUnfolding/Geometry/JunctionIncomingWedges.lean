import SixVertexUnfolding.Geometry.IncidentWedgeTransitions

/-! The coordinate-free incoming wedge is exactly the wedge assigned to
the corresponding gap in the actual circular junction order. -/

namespace SixVertexUnfolding.ConvexPolyhedron.JunctionFan

open Real Set EuclideanGeometry Wedge

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a}
    {u : T.vertices} (fan : JunctionFan T u)

/-- The corner of an incident triangle is half its actual source gap. -/
theorem gap_corner (m : circularGapMidpoints fan.order.angles fan.order.first fan.order.last)
    {α β : ℝ} (gap : IsCircularGap fan.order.angles fan.order.first fan.order.last α β)
    (midpoint : (m : ℝ) = (α + β) / 2) :
    angle (fan.triangles m).model.first (fan.triangles m).model.left
      (fan.triangles m).model.right = (β - α) / 2 := by
  obtain ⟨ordered, width, _, _, first, second, empty_gap⟩ := circular_gap_spec
    fan.order.sites fan.order.angles fan.order.increasing fan.order.bounds fan.order.chart.origin
    (P.surfaceDist a (T.vertexTarget u)) fan.order.position fan.order.first fan.order.last
    fan.order.at_first fan.order.at_last fan.order.two gap
  have on_ray (ρ : ℝ) (hr : ρ ∈ Ioo (0 : ℝ) fan.order.radius) :
      fan.order.chart.map (fan.order.chart.origin + ρ • direction ((α + β) / 2)) ∈
        openSegment ℝ (T.vertexTarget u : Space) ((fan.order.neighbors m).val : Space) := by
    rw [← midpoint]
    exact fan.order.rays m ρ hr
  exact (fan.order.chart.incident_gap_junction_angles T (fan.order.neighbors m).property rfl
    (fan.triangles m).model ordered width first second empty_gap fan.order.radius_positive on_ray).1

/-- The intrinsic triangle description reproduces the original polar gap exactly. -/
theorem incoming_wedge_eq
    (m : circularGapMidpoints fan.order.angles fan.order.first fan.order.last)
    {α β : ℝ} (gap : IsCircularGap fan.order.angles fan.order.first fan.order.last α β)
    (midpoint : (m : ℝ) = (α + β) / 2) (ω : ℝ) :
    (fan.triangles m).incomingWedge ω =
      {x | x - fan.order.chart.origin ∈ polarRegion (P.surfaceDist a (T.vertexTarget u)) ω α β} := by
  unfold IncidentTriangles.incomingWedge
  rw [fan.gap_corner m gap midpoint, midpoint,
    show (α + β) / 2 - (β - α) / 2 = α by ring,
    show (α + β) / 2 + (β - α) / 2 = β by ring]

end SixVertexUnfolding.ConvexPolyhedron.JunctionFan
