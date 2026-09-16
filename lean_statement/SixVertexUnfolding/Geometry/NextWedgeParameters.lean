import SixVertexUnfolding.Geometry.CenteredWedgeFrames
import SixVertexUnfolding.Geometry.JunctionGapAngles
import SixVertexUnfolding.Geometry.CutEdgeCornerAngles

/-! The updated wedge has the radius and corner angle of the actual
triangle at the next endpoint. These parameters do not depend on a chart. -/

namespace SixVertexUnfolding

open Real Set EuclideanGeometry

/-- The ray back to the preceding root is the opposite of the outgoing ray. -/
theorem next_root_back_ray (z : Plane) (L m : ℝ) :
    (z + L • direction m) + L • direction (m + π) = z := by
  rw [direction_add_pi, smul_neg, add_neg_cancel_right]

/-- The updated half-gap is the ordinary corner angle at the next root. -/
theorem next_root_corner (z : Plane) {L D Θ m : ℝ}
    (length_positive : 0 < L) (radius_positive : 0 < D)
    (theta_positive : 0 < Θ) (theta_small : Θ < π) :
    angle ((z + L • direction m) + D • direction (Θ + m))
      (z + L • direction m) z = π - Θ := by
  let y := z + L • direction m
  have back : y + L • direction (m + π) = z := next_root_back_ray z L m
  change angle (y + D • direction (Θ + m)) y z = _
  rw [← back]
  have translated := angle_const_add y (D • direction (Θ + m)) 0 (L • direction (m + π))
  simp only [add_zero] at translated
  rw [translated, radial_angle D L (Θ + m) (m + π) radius_positive length_positive
    (by linarith) (by linarith)]
  ring

namespace ConvexPolyhedron.CutVoronoiChart

variable {P : ConvexPolyhedron} {a b : frontier P.body} (chart : P.CutVoronoiChart a b)

/-- The numerical parameters returned by a wedge step are the next endpoint's
actual source distance and the complementary angle of its radial triangle. -/
theorem next_wedge_parameters (T : P.CutLocusTree a)
    {u v : T.vertices} (edge : T.graph.Adj u v) (at_junction : T.vertexTarget u = b)
    (M : CutEdgeMetricModel T edge)
    {γ δ ε D Θ : ℝ} (ordered : γ < δ) (one_turn : δ < γ + 2 * π)
    (first : chart.origin + P.surfaceDist a b • direction γ ∈ chart.sources)
    (second : chart.origin + P.surfaceDist a b • direction δ ∈ chart.sources)
    (empty_gap : ∀ p ∈ chart.sources, ∃ φ ∈ Icc δ (γ + 2 * π),
      p = chart.origin + P.surfaceDist a b • direction φ)
    (positive : 0 < ε)
    (on_ray : ∀ ρ ∈ Ioo (0 : ℝ) ε,
      chart.map (chart.origin + ρ • direction ((γ + δ) / 2)) ∈
        openSegment ℝ (b : Space) (v : Space))
    (radius_positive : 0 < D) (theta_positive : 0 < Θ) (theta_small : Θ < π)
    (source_position : chart.origin + P.surfaceDist a b • direction δ =
      (chart.origin + dist (b : Space) (v : Space) • direction ((γ + δ) / 2)) +
        D • direction (Θ + (γ + δ) / 2)) :
    D = P.surfaceDist a (T.vertexTarget v) ∧
      π - Θ = angle M.first M.right M.left := by
  obtain ⟨motion, at_left, at_right, _, at_source⟩ := chart.incident_metric_placement T edge
    at_junction M ordered one_turn first second empty_gap positive on_ray
  have length_positive : 0 < dist (b : Space) (v : Space) := by
    apply dist_pos.mpr
    intro same
    exact edge.ne (Subtype.ext ((congrArg Subtype.val at_junction).trans same))
  have radius := motion.dist_map M.second M.right
  rw [at_source, at_right, source_position, dist_eq_norm, add_sub_cancel_left, norm_smul,
    direction_norm, mul_one, Real.norm_eq_abs, abs_of_pos radius_positive] at radius
  have actual : dist M.second M.right = P.surfaceDist a (T.vertexTarget v) := by
    simpa [T.closedEdgeTarget_one] using M.second_distances 1
  refine ⟨radius.trans actual, ?_⟩
  have corner := motion.toAffineIsometry.angle_map M.second M.right M.left
  change angle (motion M.second) (motion M.right) (motion M.left) = _ at corner
  rw [at_source, at_right, at_left, source_position,
    next_root_corner chart.origin length_positive radius_positive theta_positive theta_small] at corner
  exact corner.trans M.paired_corner_angles.2.symm

end ConvexPolyhedron.CutVoronoiChart
end SixVertexUnfolding
