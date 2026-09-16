import SixVertexUnfolding.Geometry.OctahedralPatchDirections

/-! Each face corner is strictly between zero and pi; a two-face corner is below a full turn. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.DevelopedPatch

open Real EuclideanGeometry

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph} {source : Fin 6} {sector : Fin 4}
variable (patch : graph.DevelopedPatch source sector)

theorem left_face_angle_bounds :
    0 < angle patch.pole patch.left patch.right ∧ angle patch.pole patch.left patch.right < π ∧
    0 < angle patch.right patch.left patch.apex ∧ angle patch.right patch.left patch.apex < π := by
  have fan : ¬ Collinear ℝ ({patch.pole, patch.left, patch.right} : Set Plane) := by
    have reorder : ({patch.pole, patch.left, patch.right} : Set Plane) = {patch.left, patch.right, patch.pole} := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [reorder]
    exact patch.fan_noncollinear
  have petal : ¬ Collinear ℝ ({patch.right, patch.left, patch.apex} : Set Plane) := by
    simpa only [Set.insert_comm] using patch.petal_noncollinear
  exact ⟨angle_pos_of_not_collinear fan, angle_lt_pi_of_not_collinear fan,
    angle_pos_of_not_collinear petal, angle_lt_pi_of_not_collinear petal⟩

theorem right_face_angle_bounds :
    0 < angle patch.pole patch.right patch.left ∧ angle patch.pole patch.right patch.left < π ∧
    0 < angle patch.left patch.right patch.apex ∧ angle patch.left patch.right patch.apex < π := by
  have fan : ¬ Collinear ℝ ({patch.pole, patch.right, patch.left} : Set Plane) := by
    have reorder : ({patch.pole, patch.right, patch.left} : Set Plane) = {patch.left, patch.right, patch.pole} := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [reorder]
    exact patch.fan_noncollinear
  exact ⟨angle_pos_of_not_collinear fan, angle_lt_pi_of_not_collinear fan,
    angle_pos_of_not_collinear patch.petal_noncollinear, angle_lt_pi_of_not_collinear patch.petal_noncollinear⟩

theorem leftCorner_lt_two_pi : patch.leftCorner < 2 * π := by
  have bounds := patch.left_face_angle_bounds
  unfold leftCorner
  linarith [bounds.2.1, bounds.2.2.2]

theorem rightCorner_lt_two_pi : patch.rightCorner < 2 * π := by
  have bounds := patch.right_face_angle_bounds
  unfold rightCorner
  linarith [bounds.2.1, bounds.2.2.2]

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.DevelopedPatch
