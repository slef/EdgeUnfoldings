import SixVertexUnfolding.Geometry.JunctionMetricTriangles
import SixVertexUnfolding.Geometry.CutEdgeSourceAngles
import SixVertexUnfolding.Geometry.RadialHinges

/-! The apex angle in the common junction chart is the source angle of
the actual metric kite. This connects its later sum to the wedge budget.
-/

namespace SixVertexUnfolding.ConvexPolyhedron.CutVoronoiChart

open Real Set EuclideanGeometry

variable {P : ConvexPolyhedron} {a b : frontier P.body} (chart : P.CutVoronoiChart a b)

/-- The upper gap endpoint contributes exactly the metric kite's source angle. -/
theorem incident_gap_source_angle (T : P.CutLocusTree a)
    {u v : T.vertices} (edge : T.graph.Adj u v) (at_junction : T.vertexTarget u = b)
    (M : CutEdgeMetricModel T edge)
    {α β ε : ℝ} (ordered : α < β) (one_turn : β < α + 2 * π)
    (first : chart.origin + P.surfaceDist a b • direction α ∈ chart.sources)
    (second : chart.origin + P.surfaceDist a b • direction β ∈ chart.sources)
    (empty_gap : ∀ p ∈ chart.sources, ∃ φ ∈ Icc β (α + 2 * π),
      p = chart.origin + P.surfaceDist a b • direction φ)
    (positive : 0 < ε)
    (on_ray : ∀ ρ ∈ Ioo (0 : ℝ) ε,
      chart.map (chart.origin + ρ • direction ((α + β) / 2)) ∈
        openSegment ℝ (b : Space) (v : Space)) :
    angle chart.origin (chart.origin + P.surfaceDist a b • direction β)
      (chart.origin + dist (b : Space) (v : Space) • direction ((α + β) / 2)) = M.sourceAngle := by
  obtain ⟨motion, at_left, at_right, _, at_source⟩ := chart.incident_metric_placement T edge
    at_junction M ordered one_turn first second empty_gap positive on_ray
  have preserved := motion.toAffineIsometry.angle_map M.left M.second M.right
  change angle (motion M.left) (motion M.second) (motion M.right) = angle M.left M.second M.right at preserved
  rwa [at_left, at_source, at_right, M.second_sourceAngle] at preserved

/-- The two corners at the junction each occupy half of the assigned
source gap. Thus their sum counts that gap exactly once. -/
theorem incident_gap_junction_angles (T : P.CutLocusTree a)
    {u v : T.vertices} (edge : T.graph.Adj u v) (at_junction : T.vertexTarget u = b)
    (M : CutEdgeMetricModel T edge)
    {α β ε : ℝ} (ordered : α < β) (one_turn : β < α + 2 * π)
    (first : chart.origin + P.surfaceDist a b • direction α ∈ chart.sources)
    (second : chart.origin + P.surfaceDist a b • direction β ∈ chart.sources)
    (empty_gap : ∀ p ∈ chart.sources, ∃ φ ∈ Icc β (α + 2 * π),
      p = chart.origin + P.surfaceDist a b • direction φ)
    (positive : 0 < ε)
    (on_ray : ∀ ρ ∈ Ioo (0 : ℝ) ε,
      chart.map (chart.origin + ρ • direction ((α + β) / 2)) ∈
        openSegment ℝ (b : Space) (v : Space)) :
    angle M.first M.left M.right = (β - α) / 2 ∧
      angle M.second M.left M.right = (β - α) / 2 := by
  obtain ⟨motion, at_left, at_right, at_first, at_second⟩ := chart.incident_metric_placement T edge
    at_junction M ordered one_turn first second empty_gap positive on_ray
  have source_positive : 0 < P.surfaceDist a b := by
    simpa using tail_radius_pos (at_junction ▸ T.vertexTarget_different u) (0 : unitInterval)
      (by change (0 : ℝ) < 1; norm_num)
  have length_positive : 0 < dist (b : Space) (v : Space) := by
    apply dist_pos.mpr
    intro same
    exact edge.ne (Subtype.ext ((congrArg Subtype.val at_junction).trans same))
  have translated (x y : Plane) : angle (chart.origin + x) chart.origin (chart.origin + y) =
      angle x 0 y := by simpa using angle_const_add chart.origin x 0 y
  have left_angle := motion.toAffineIsometry.angle_map M.first M.left M.right
  have right_angle := motion.toAffineIsometry.angle_map M.second M.left M.right
  change angle (motion M.first) (motion M.left) (motion M.right) = _ at left_angle
  change angle (motion M.second) (motion M.left) (motion M.right) = _ at right_angle
  rw [at_first, at_left, at_right, translated,
    radial_angle _ _ _ _ source_positive length_positive (by linarith) (by linarith)] at left_angle
  rw [at_second, at_left, at_right, translated, angle_comm,
    radial_angle _ _ _ _ length_positive source_positive (by linarith) (by linarith)] at right_angle
  constructor <;> linarith

end SixVertexUnfolding.ConvexPolyhedron.CutVoronoiChart
