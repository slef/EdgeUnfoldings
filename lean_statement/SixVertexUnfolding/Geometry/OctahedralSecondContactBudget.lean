import SixVertexUnfolding.Geometry.OctahedralSecondContactSine
import SixVertexUnfolding.Geometry.OctahedralFirstContactBudget

/-! The strict contact budget at the second remote petal uses the last fan triangle's slit corner. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open Real EuclideanGeometry OctahedralTriangles

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

/-- The mirrored E2 budget includes contact at the copied apex and uses the actual strict spatial link. -/
theorem second_cut_contact_curvature_budget
    (alternative : π ≤ graph.curvature source ∨ graph.curvature (opposite source) ≤ π)
    (threshold : π ≤ 2 * graph.curvature (fanNeighbor source slit) + graph.curvature (opposite source))
    (t : ℝ) (positive : 0 < t) (upper : t ≤ 1)
    (contact : (net.patch 2).right + t • ((net.patch 2).apex - (net.patch 2).right) ∈
      segment ℝ 0 (net.patch 0).left) :
    graph.curvature (fanNeighbor source (slit + 3)) + graph.curvature (fanNeighbor source slit) +
      2 * graph.curvature (opposite source) +
      2 * angle (net.patch 3).right (net.patch 3).left (net.patch 3).apex < π := by
  have contact_bound := net.second_cut_contact_angle_bound alternative threshold t positive upper contact
  have angle_sum : (net.patch 3).leftCorner + (2 * π - graph.openingAngle (opposite source) slit 3) =
      π - angle (net.patch 3).pole (net.patch 3).right (net.patch 3).left +
        angle (net.patch 3).right (net.patch 3).left (net.patch 3).apex + graph.curvature (opposite source) := by
    have total := angle_add_angle_add_angle_eq_pi (net.patch 3).left
      (ne₂₃_of_not_collinear (net.patch 3).fan_noncollinear)
    rw [net.patch_fan_pole_angle] at total
    change _ + _ + (graph.openingAngle (opposite source) slit 4 - graph.openingAngle (opposite source) slit 3) = π at total
    rw [graph.openingAngle_last] at total
    have commute := angle_comm (net.patch 3).right (net.patch 3).left (net.patch 3).pole
    unfold DevelopedPatch.leftCorner curvature
    linarith
  have strict_link := net.fan_right_corner_link 3
  rw [add_assoc, show (3 : Fin 4) + 1 = 0 by decide, add_zero] at strict_link
  exact Curvature.finite_contact_budget contact_bound angle_sum strict_link

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
