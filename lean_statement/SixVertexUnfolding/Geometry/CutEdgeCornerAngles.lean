import SixVertexUnfolding.Geometry.CutEdgeSourceAngles
import Mathlib.Geometry.Euclidean.Triangle

/-! Angle accounting for the actual metric triangles. Reversing a tree
edge exchanges its endpoint corners and preserves its source angle,
regardless of the coordinate models chosen at the two ends. -/

namespace SixVertexUnfolding.ConvexPolyhedron.CutEdgeMetricModel

open Set EuclideanGeometry

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a}
  {u v : T.vertices} {edge : T.graph.Adj u v} (M : CutEdgeMetricModel T edge)

theorem left_radius : dist M.first M.left = P.surfaceDist a (T.vertexTarget u) := by
  simpa [T.closedEdgeTarget_zero] using M.first_distances 0

theorem right_radius : dist M.first M.right = P.surfaceDist a (T.vertexTarget v) := by
  simpa [T.closedEdgeTarget_one] using M.first_distances 1

/-- Both triangles have the same corner angle at each endpoint of the cut edge. -/
theorem paired_corner_angles :
    angle M.first M.left M.right = angle M.second M.left M.right ∧
      angle M.first M.right M.left = angle M.second M.right M.left := by
  obtain ⟨motion, at_source, at_left, at_right⟩ := exists_plane_motion_triangle
    M.first M.left M.right M.second M.left M.right
    (ne₁₂_of_not_collinear M.noncollinear.2) M.left_distances M.right_distances rfl
  have first := motion.toAffineIsometry.angle_map M.first M.left M.right
  have second := motion.toAffineIsometry.angle_map M.first M.right M.left
  change angle (motion M.first) (motion M.left) (motion M.right) = _ at first
  change angle (motion M.first) (motion M.right) (motion M.left) = _ at second
  rw [at_source, at_left, at_right] at first second
  exact ⟨first.symm, second.symm⟩

/-- The source angle and the two endpoint corners form one ordinary triangle. -/
theorem triangle_angle_sum :
    M.sourceAngle + angle M.first M.left M.right + angle M.first M.right M.left = Real.pi := by
  have total := angle_add_angle_add_angle_eq_pi M.right (ne₁₂_of_not_collinear M.noncollinear.1).symm
  change angle M.first M.left M.right + angle M.left M.right M.first +
    angle M.right M.first M.left = Real.pi at total
  rw [angle_comm M.left M.right M.first, angle_comm M.right M.first M.left] at total
  change angle M.left M.first M.right + _ + _ = Real.pi
  linarith

/-- Opposite orientations of the same actual edge give the same source
angle and exchange the endpoint corners, even for independent models. -/
theorem reverse_angles (N : CutEdgeMetricModel T edge.symm) :
    M.sourceAngle = N.sourceAngle ∧
      angle M.first M.left M.right = angle N.first N.right N.left ∧
      angle M.first M.right M.left = angle N.first N.left N.right := by
  have first_length : dist M.first M.left = dist N.first N.right := M.left_radius.trans N.right_radius.symm
  have second_length : dist M.first M.right = dist N.first N.left := M.right_radius.trans N.left_radius.symm
  have base : dist M.left M.right = dist N.right N.left := by
    rw [M.base_length, dist_comm N.right N.left, N.base_length, dist_comm (v : Space) (u : Space)]
  obtain ⟨motion, at_source, at_left, at_right⟩ := exists_plane_motion_triangle
    M.first M.left M.right N.first N.right N.left
    (ne₁₃_of_not_collinear N.noncollinear.1) first_length second_length base
  have source := motion.toAffineIsometry.angle_map M.left M.first M.right
  have first := motion.toAffineIsometry.angle_map M.first M.left M.right
  have second := motion.toAffineIsometry.angle_map M.first M.right M.left
  change angle (motion M.left) (motion M.first) (motion M.right) = _ at source
  change angle (motion M.first) (motion M.left) (motion M.right) = _ at first
  change angle (motion M.first) (motion M.right) (motion M.left) = _ at second
  rw [at_source, at_left, at_right, angle_comm N.right N.first N.left] at source
  rw [at_source, at_left, at_right] at first second
  exact ⟨source.symm, first.symm, second.symm⟩

/-- Independently chosen models of the same oriented edge have the same corners. -/
theorem same_edge_corner_angles (N : CutEdgeMetricModel T edge) :
    angle M.first M.left M.right = angle N.first N.left N.right ∧
      angle M.second M.left M.right = angle N.second N.left N.right := by
  obtain ⟨motion, at_source, at_left, at_right⟩ := exists_plane_motion_triangle
    M.first M.left M.right N.first N.left N.right
    (ne₁₂_of_not_collinear N.noncollinear.1) (M.left_radius.trans N.left_radius.symm)
    (M.right_radius.trans N.right_radius.symm) (M.base_length.trans N.base_length.symm)
  have first := motion.toAffineIsometry.angle_map M.first M.left M.right
  change angle (motion M.first) (motion M.left) (motion M.right) = _ at first
  rw [at_source, at_left, at_right] at first
  refine ⟨first.symm, ?_⟩
  rw [← M.paired_corner_angles.1, ← N.paired_corner_angles.1]
  exact first.symm

/-- The source angle also does not depend on the chosen coordinates. -/
theorem same_edge_sourceAngle (N : CutEdgeMetricModel T edge) : M.sourceAngle = N.sourceAngle := by
  obtain ⟨motion, at_source, at_left, at_right⟩ := exists_plane_motion_triangle
    M.first M.left M.right N.first N.left N.right
    (ne₁₂_of_not_collinear N.noncollinear.1) (M.left_radius.trans N.left_radius.symm)
    (M.right_radius.trans N.right_radius.symm) (M.base_length.trans N.base_length.symm)
  have angle := motion.toAffineIsometry.angle_map M.left M.first M.right
  change EuclideanGeometry.angle (motion M.left) (motion M.first) (motion M.right) = M.sourceAngle at angle
  rw [at_source, at_left, at_right] at angle
  exact angle.symm

end SixVertexUnfolding.ConvexPolyhedron.CutEdgeMetricModel
