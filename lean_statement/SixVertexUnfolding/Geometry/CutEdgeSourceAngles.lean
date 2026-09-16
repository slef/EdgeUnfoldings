import SixVertexUnfolding.Geometry.CutEdgeKiteGeometry
import SixVertexUnfolding.Geometry.HingeIsometries

/-! The two apex angles of an actual cut-edge kite agree. This defines
the single edge angle used in the later cumulative-angle argument. -/

namespace SixVertexUnfolding.ConvexPolyhedron.CutEdgeMetricModel

open Set EuclideanGeometry

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a}
  {u v : T.vertices} {edge : T.graph.Adj u v} (M : CutEdgeMetricModel T edge)

/-- The angle of either radial triangle at its planar source copy. -/
noncomputable def sourceAngle : ℝ := angle M.left M.first M.right

theorem sourceAngle_pos : 0 < M.sourceAngle := by
  apply angle_pos_of_not_collinear
  simpa only [insert_comm M.left] using M.noncollinear.1

theorem sourceAngle_lt_pi : M.sourceAngle < Real.pi := by
  apply angle_lt_pi_of_not_collinear
  simpa only [insert_comm M.left] using M.noncollinear.1

/-- Both sides of a kite contribute the same source angle. -/
theorem second_sourceAngle : angle M.left M.second M.right = M.sourceAngle := by
  obtain ⟨motion, at_source, at_left, at_right⟩ := exists_plane_motion_triangle
    M.first M.left M.right M.second M.left M.right
    (ne₁₂_of_not_collinear M.noncollinear.2)
    M.left_distances M.right_distances rfl
  have preserved := motion.toAffineIsometry.angle_map M.left M.first M.right
  change angle (motion M.left) (motion M.first) (motion M.right) = M.sourceAngle at preserved
  rwa [at_left, at_source, at_right] at preserved

end SixVertexUnfolding.ConvexPolyhedron.CutEdgeMetricModel
