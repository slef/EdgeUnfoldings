import SixVertexUnfolding.Geometry.OctahedralOppositeAngles

/-! The two fan corners adjacent to the middle base determine the Case B cone widths. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open Real EuclideanGeometry

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

noncomputable def leftFanCorner (i : Fin 2) : ℝ :=
  angle (net.patch i.castSucc.castSucc).pole (net.patch i.castSucc.castSucc).right (net.patch i.castSucc.castSucc).left +
    angle (net.patch i.castSucc.succ).pole (net.patch i.castSucc.succ).left (net.patch i.castSucc.succ).right

noncomputable def rightFanCorner (i : Fin 2) : ℝ :=
  angle (net.patch i.castSucc.succ).pole (net.patch i.castSucc.succ).right (net.patch i.castSucc.succ).left +
    angle (net.patch i.succ.succ).pole (net.patch i.succ.succ).left (net.patch i.succ.succ).right

theorem leftFanCorner_pos (i : Fin 2) : 0 < net.leftFanCorner i := by
  have noncollinear : ¬ Collinear ℝ ({(net.patch i.castSucc.succ).pole, (net.patch i.castSucc.succ).left,
      (net.patch i.castSucc.succ).right} : Set Plane) := by
    have reorder : ({(net.patch i.castSucc.succ).pole, (net.patch i.castSucc.succ).left,
        (net.patch i.castSucc.succ).right} : Set Plane) =
        {(net.patch i.castSucc.succ).left, (net.patch i.castSucc.succ).right, (net.patch i.castSucc.succ).pole} := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [reorder]
    exact (net.patch i.castSucc.succ).fan_noncollinear
  have positive := angle_pos_of_not_collinear noncollinear
  have nonnegative := angle_nonneg (net.patch i.castSucc.castSucc).pole (net.patch i.castSucc.castSucc).right (net.patch i.castSucc.castSucc).left
  unfold leftFanCorner
  linarith

theorem rightFanCorner_pos (i : Fin 2) : 0 < net.rightFanCorner i := by
  have noncollinear : ¬ Collinear ℝ ({(net.patch i.castSucc.succ).pole, (net.patch i.castSucc.succ).right,
      (net.patch i.castSucc.succ).left} : Set Plane) := by
    have reorder : ({(net.patch i.castSucc.succ).pole, (net.patch i.castSucc.succ).right,
        (net.patch i.castSucc.succ).left} : Set Plane) =
        {(net.patch i.castSucc.succ).left, (net.patch i.castSucc.succ).right, (net.patch i.castSucc.succ).pole} := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [reorder]
    exact (net.patch i.castSucc.succ).fan_noncollinear
  have positive := angle_pos_of_not_collinear noncollinear
  have nonnegative := angle_nonneg (net.patch i.succ.succ).pole (net.patch i.succ.succ).left (net.patch i.succ.succ).right
  unfold rightFanCorner
  linarith

theorem left_base_angle_sum (i : Fin 2) : net.widenedLeft i + net.leftFanCorner i +
    angle (net.patch i.castSucc.castSucc).left (net.patch i.castSucc.castSucc).right (net.patch i.castSucc.castSucc).apex = 2 * π := by
  have total := net.junction_corner_sum i.castSucc
  unfold DevelopedPatch.leftCorner DevelopedPatch.rightCorner at total
  unfold widenedLeft leftFanCorner curvature
  linarith

theorem right_base_angle_sum (i : Fin 2) : net.widenedRight i + net.rightFanCorner i +
    angle (net.patch i.succ.succ).right (net.patch i.succ.succ).left (net.patch i.succ.succ).apex = 2 * π := by
  have total := net.junction_corner_sum i.succ
  rw [show i.succ.castSucc = i.castSucc.succ from rfl] at total
  unfold DevelopedPatch.leftCorner DevelopedPatch.rightCorner at total
  unfold widenedRight rightFanCorner curvature
  linarith

theorem left_base_cone_bounds (i : Fin 2) :
    π < net.widenedLeft i + net.leftFanCorner i ∧ net.widenedLeft i + net.leftFanCorner i < 2 * π := by
  have total := net.left_base_angle_sum i
  have positive := angle_pos_of_not_collinear (net.patch i.castSucc.castSucc).petal_noncollinear
  have small := angle_lt_pi_of_not_collinear (net.patch i.castSucc.castSucc).petal_noncollinear
  constructor <;> linarith

theorem right_base_cone_bounds (i : Fin 2) :
    π < net.widenedRight i + net.rightFanCorner i ∧ net.widenedRight i + net.rightFanCorner i < 2 * π := by
  have total := net.right_base_angle_sum i
  have noncollinear : ¬ Collinear ℝ ({(net.patch i.succ.succ).right, (net.patch i.succ.succ).left,
      (net.patch i.succ.succ).apex} : Set Plane) := by
    simpa only [Set.insert_comm] using (net.patch i.succ.succ).petal_noncollinear
  have positive := angle_pos_of_not_collinear noncollinear
  have small := angle_lt_pi_of_not_collinear noncollinear
  constructor <;> linarith

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
