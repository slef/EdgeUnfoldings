import SixVertexUnfolding.Geometry.OctahedralPocketFan
import SixVertexUnfolding.Geometry.QuadrilateralOrientation

/-! The constructed pocket is clockwise in the actual fan coordinates, in both overlap orientations. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open Real OctahedralTriangles

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

/-- Containment of the first fan fixes the orientation of the last-triple boundary. -/
theorem last_pocket_clockwise
    (source_order : graph.curvature (opposite source) ≤ graph.curvature source)
    (maximal : ∀ i, graph.curvature (fanNeighbor source i) ≤ graph.curvature (fanNeighbor source slit))
    (small : net.leftFanCorner 1 + net.rightFanCorner 1 < π)
    (p : Plane) (left : p ∈ net.placedTriangle (true, 1)) (right : p ∈ net.placedTriangle (true, 3))
    (boundary : QuadrilateralBoundary (net.patch 1).left p (net.patch 3).right 0)
    (diagonal : det ((net.patch 3).right - (net.patch 1).left) (p - (net.patch 1).left) *
        det ((net.patch 3).right - (net.patch 1).left) (0 - (net.patch 1).left) < 0 ∨
      det (0 - p) ((net.patch 1).left - p) * det (0 - p) ((net.patch 3).right - p) < 0) :
    (0 < det ((net.patch 3).right - (net.patch 1).left) (p - (net.patch 1).left) ∧
      det ((net.patch 3).right - (net.patch 1).left) (0 - (net.patch 1).left) < 0) ∨
    (det (0 - p) ((net.patch 1).left - p) < 0 ∧ 0 < det (0 - p) ((net.patch 3).right - p)) := by
  have fan := net.first_fan_in_last_pocket source_order maximal small p left right boundary diagonal
  have shared : (net.patch 0).right = (net.patch 1).left := net.consecutive_patch_corner 0
  apply quadrilateral_clockwise_of_right_triangle _ p _ 0 (net.patch 0).left diagonal
  · intro x member
    apply fan
    rw [net.placedTriangle_hull]
    change x ∈ convexHull ℝ ({(net.patch 0).left, (net.patch 0).right, (net.patch 0).pole} : Set Plane)
    rw [net.patch_pole, shared]
    apply convexHull_mono _ member
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at *
    tauto
  · have area := net.patch_fan_area_pos 0
    rw [net.patch_pole, shared] at area
    have identity : det ((net.patch 1).left - 0) ((net.patch 0).left - 0) =
        -det ((net.patch 1).left - (net.patch 0).left) (0 - (net.patch 0).left) := by
      simp only [det, PiLp.sub_apply, PiLp.zero_apply]
      ring
    rw [identity]
    exact neg_neg_of_pos area

/-- Containment of the last fan fixes the orientation of the reflected first-triple boundary. -/
theorem first_pocket_clockwise
    (source_order : graph.curvature (opposite source) ≤ graph.curvature source)
    (maximal : ∀ i, graph.curvature (fanNeighbor source i) ≤ graph.curvature (fanNeighbor source slit))
    (small : net.leftFanCorner 0 + net.rightFanCorner 0 < π)
    (p : Plane) (left : p ∈ net.placedTriangle (true, 0)) (right : p ∈ net.placedTriangle (true, 2))
    (boundary : QuadrilateralBoundary (net.patch 0).left p (net.patch 2).right 0)
    (diagonal : det ((net.patch 2).right - (net.patch 0).left) (p - (net.patch 0).left) *
        det ((net.patch 2).right - (net.patch 0).left) (0 - (net.patch 0).left) < 0 ∨
      det (0 - p) ((net.patch 0).left - p) * det (0 - p) ((net.patch 2).right - p) < 0) :
    (0 < det ((net.patch 2).right - (net.patch 0).left) (p - (net.patch 0).left) ∧
      det ((net.patch 2).right - (net.patch 0).left) (0 - (net.patch 0).left) < 0) ∨
    (det (0 - p) ((net.patch 0).left - p) < 0 ∧ 0 < det (0 - p) ((net.patch 2).right - p)) := by
  have fan := net.last_fan_in_first_pocket source_order maximal small p left right boundary diagonal
  have shared : (net.patch 2).right = (net.patch 3).left := net.consecutive_patch_corner 2
  apply quadrilateral_clockwise_of_left_triangle _ p _ 0 (net.patch 3).right diagonal
  · intro x member
    apply fan
    rw [net.placedTriangle_hull]
    change x ∈ convexHull ℝ ({(net.patch 3).left, (net.patch 3).right, (net.patch 3).pole} : Set Plane)
    rw [net.patch_pole, ← shared]
    apply convexHull_mono _ member
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at *
    tauto
  · have area := net.patch_fan_area_pos 3
    rw [net.patch_pole, ← shared] at area
    have identity : det ((net.patch 2).right - 0) ((net.patch 3).right - 0) =
        det ((net.patch 3).right - (net.patch 2).right) (0 - (net.patch 2).right) := by
      simp only [det, PiLp.sub_apply, PiLp.zero_apply]
      ring
    rwa [identity]

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
