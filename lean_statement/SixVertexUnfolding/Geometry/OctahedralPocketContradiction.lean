import SixVertexUnfolding.Geometry.OctahedralPocketOrientation
import SixVertexUnfolding.Geometry.OctahedralPocketAngleIdentities
import SixVertexUnfolding.Geometry.OctahedralPocketBudget

/-! A small-fan overlap would require more angle at the omitted petal apex than its curvature budget allows. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open Real OctahedralTriangles

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

/-- The last pair of opposite petals cannot overlap in the small-fan case. -/
theorem last_opposite_petals_of_small_fan
    (source_order : graph.curvature (opposite source) ≤ graph.curvature source)
    (maximal : ∀ i, graph.curvature (fanNeighbor source i) ≤ graph.curvature (fanNeighbor source slit))
    (small : net.leftFanCorner 1 + net.rightFanCorner 1 < π) : net.Separated (true, 1) (true, 3) := by
  by_contra overlap
  obtain ⟨p, left, right, boundary, diagonal⟩ := net.exists_last_pocket_diagonal source_order maximal overlap
  have orientation := net.last_pocket_clockwise source_order maximal small p
    (interior_subset left) (interior_subset right) boundary diagonal
  have total := clockwise_quadrilateral_angle_sum (net.patch 1).left p (net.patch 3).right 0 orientation
  have contact := clockwise_quadrilateral_contact_pos (net.patch 1).left p (net.patch 3).right 0 orientation
  have distinct := boundary.corners_distinct
  have at_left := net.petal_left_exterior_corner 1 p (interior_subset left) distinct.1.symm
  have at_right := net.petal_right_exterior_corner 3 p (interior_subset right) distinct.2.2.2.1
  have at_pole := net.last_pocket_pole_corner
  have junction := net.junction_corner_sum 0
  change (net.patch 0).rightCorner + (net.patch 1).leftCorner =
    graph.totalAngleAt (fanNeighbor source ((slit + 0) + 1)) at junction
  simp only [add_zero] at junction
  have slit_sum := net.slit_corner_sum
  have patch_sum := net.patch_corner_angle_sum 0
  change (net.patch 0).leftCorner + (net.patch 0).rightCorner +
    (graph.openingAngle (opposite source) slit 1 - 0) + net.petalApexAngle 0 = 2 * π at patch_sum
  have budget := (net.selected_pocket_angle_bounds maximal).1
  unfold curvature at at_pole budget
  linarith

/-- The reflected first pair is excluded by the omitted last petal's angle budget. -/
theorem first_opposite_petals_of_small_fan
    (source_order : graph.curvature (opposite source) ≤ graph.curvature source)
    (maximal : ∀ i, graph.curvature (fanNeighbor source i) ≤ graph.curvature (fanNeighbor source slit))
    (small : net.leftFanCorner 0 + net.rightFanCorner 0 < π) : net.Separated (true, 0) (true, 2) := by
  by_contra overlap
  obtain ⟨p, left, right, boundary, diagonal⟩ := net.exists_first_pocket_diagonal source_order maximal overlap
  have orientation := net.first_pocket_clockwise source_order maximal small p
    (interior_subset left) (interior_subset right) boundary diagonal
  have total := clockwise_quadrilateral_angle_sum (net.patch 0).left p (net.patch 2).right 0 orientation
  have contact := clockwise_quadrilateral_contact_pos (net.patch 0).left p (net.patch 2).right 0 orientation
  have distinct := boundary.corners_distinct
  have at_left := net.petal_left_exterior_corner 0 p (interior_subset left) distinct.1.symm
  have at_right := net.petal_right_exterior_corner 2 p (interior_subset right) distinct.2.2.2.1
  have at_pole := net.first_pocket_pole_corner
  have junction := net.junction_corner_sum 2
  change (net.patch 2).rightCorner + (net.patch 3).leftCorner =
    graph.totalAngleAt (fanNeighbor source ((slit + 2) + 1)) at junction
  rw [add_assoc, show (2 : Fin 4) + 1 = 3 by decide] at junction
  have slit_sum := net.slit_corner_sum
  have patch_sum := net.patch_corner_angle_sum 3
  change (net.patch 3).leftCorner + (net.patch 3).rightCorner +
    (graph.openingAngle (opposite source) slit 4 - graph.openingAngle (opposite source) slit 3) +
    net.petalApexAngle 3 = 2 * π at patch_sum
  have budget := (net.selected_pocket_angle_bounds maximal).2
  unfold curvature at at_pole budget
  linarith

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
