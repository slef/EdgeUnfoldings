import SixVertexUnfolding.Geometry.OctahedralPetalExteriorCorners
import SixVertexUnfolding.Geometry.OctahedralPairedBounds
import SixVertexUnfolding.Geometry.OctahedralFanSeeds

/-! The patch angle sum and the two exact pole corners needed by the pocket contradiction. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open Real EuclideanGeometry OctahedralTriangles

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

/-- Adding the two face sums gives the four angles of one developed patch. -/
theorem patch_corner_angle_sum (i : Fin 4) :
    (net.patch i).leftCorner + (net.patch i).rightCorner +
      (graph.openingAngle (opposite source) slit i.succ - graph.openingAngle (opposite source) slit i.castSucc) +
      net.petalApexAngle i = 2 * π := by
  have fan := angle_add_angle_add_angle_eq_pi (net.patch i).right
    (ne₁₃_of_not_collinear (net.patch i).fan_noncollinear)
  rw [angle_comm (net.patch i).right (net.patch i).pole (net.patch i).left,
    angle_comm (net.patch i).left (net.patch i).right (net.patch i).pole,
    net.patch_fan_pole_angle] at fan
  have petal := net.petal_base_angle_sum i
  unfold DevelopedPatch.leftCorner DevelopedPatch.rightCorner
  linarith

/-- The last pocket's pole corner is the omitted first fan angle plus the pole curvature. -/
theorem last_pocket_pole_corner : clockwiseCorner (net.patch 3).right 0 (net.patch 1).left =
    graph.openingAngle (opposite source) slit 1 + graph.curvature (opposite source) := by
  have angles := opening_angles_ordered (graph := graph) (small_faces := small_faces) (source := source) (slit := slit)
  let θ := graph.openingAngle (opposite source) slit
  let R := fun i => dist (graph.vertex (opposite source) : Space)
    (graph.vertex (openingVertex (opposite source) slit i))
  have measured := counterclockwiseAngle_polar (R 4) (R 1) (θ 4) (θ 1 + 2 * π)
    (graph.opening_radius_pos _ _ _) (graph.opening_radius_pos _ _ _)
    (by dsimp [θ]; linarith [angles.1, angles.2.2.2.2])
    (by dsimp [θ]; linarith [angles.2.1, angles.2.2.1, angles.2.2.2.1])
  rw [direction_add_two_pi] at measured
  have total := graph.openingAngle_last (opposite source) slit
  unfold clockwiseCorner
  rw [sub_zero, sub_zero, net.patch_right, net.patch_left]
  change counterclockwiseAngle (R 4 • direction (θ 4)) (R 1 • direction (θ 1)) = _
  rw [measured]
  dsimp [θ]
  unfold curvature
  linarith

/-- The first pocket's pole corner is the omitted last fan angle plus the pole curvature. -/
theorem first_pocket_pole_corner : clockwiseCorner (net.patch 2).right 0 (net.patch 0).left =
    graph.openingAngle (opposite source) slit 4 - graph.openingAngle (opposite source) slit 3 +
      graph.curvature (opposite source) := by
  have angles := opening_angles_ordered (graph := graph) (small_faces := small_faces) (source := source) (slit := slit)
  let θ := graph.openingAngle (opposite source) slit
  let R := fun i => dist (graph.vertex (opposite source) : Space)
    (graph.vertex (openingVertex (opposite source) slit i))
  have measured := counterclockwiseAngle_polar (R 3) (R 0) (θ 3) (θ 0 + 2 * π)
    (graph.opening_radius_pos _ _ _) (graph.opening_radius_pos _ _ _)
    (by dsimp [θ]; linarith [angles.2.2.2.1, angles.2.2.2.2])
    (by dsimp [θ]; linarith [angles.1, angles.2.1, angles.2.2.1])
  rw [direction_add_two_pi] at measured
  have total := graph.openingAngle_last (opposite source) slit
  unfold clockwiseCorner
  rw [sub_zero, sub_zero, net.patch_right, net.patch_left]
  change counterclockwiseAngle (R 3 • direction (θ 3)) (R 0 • direction (θ 0)) = _
  rw [measured]
  dsimp [θ]
  change 0 + 2 * π - graph.openingAngle (opposite source) slit 3 = _
  unfold curvature
  linarith

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
