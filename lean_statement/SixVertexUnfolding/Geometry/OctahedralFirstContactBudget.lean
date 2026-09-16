import SixVertexUnfolding.Geometry.OctahedralFirstContactSine

/-! The actual strict link at the slit turns finite contact into a strict curvature budget. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open Real EuclideanGeometry OctahedralTriangles

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

theorem fan_left_corner_link (i : Fin 4) :
    2 * angle (net.patch i).pole (net.patch i).left (net.patch i).right <
      2 * π - graph.curvature (fanNeighbor source (slit + i)) := by
  rw [(net.patch i).fan_angle_at_left]
  apply graph.vertex_angle_lt_half_deficit small_faces
  · exact (by decide : ∀ s j, opposite s ≠ fanNeighbor s j) source (slit + i)
  · exact (by decide : ∀ s j, fanNeighbor s (j + 1) ≠ fanNeighbor s j) source (slit + i)
  · exact (by decide : ∀ s j, opposite s ≠ opposite (fanNeighbor s j)) source (slit + i)

theorem fan_right_corner_link (i : Fin 4) :
    2 * angle (net.patch i).pole (net.patch i).right (net.patch i).left <
      2 * π - graph.curvature (fanNeighbor source ((slit + i) + 1)) := by
  rw [angle_comm, (net.patch i).fan_angle_at_right]
  apply graph.vertex_angle_lt_half_deficit small_faces
  · exact (by decide : ∀ s j, fanNeighbor s j ≠ fanNeighbor s (j + 1)) source (slit + i)
  · exact (by decide : ∀ s j, opposite s ≠ fanNeighbor s (j + 1)) source (slit + i)
  · exact (by decide : ∀ s j, fanNeighbor s j ≠ opposite (fanNeighbor s (j + 1))) source (slit + i)

/-- The strict curvature obstruction E2 now follows from an actual first copied-edge contact. -/
theorem first_cut_contact_curvature_budget
    (alternative : π ≤ graph.curvature source ∨ graph.curvature (opposite source) ≤ π)
    (threshold : π ≤ 2 * graph.curvature (fanNeighbor source slit) + graph.curvature (opposite source))
    (t : ℝ) (positive : 0 < t) (upper : t ≤ 1)
    (contact : (net.patch 0).right + t • ((net.patch 1).apex - (net.patch 0).right) ∈
      segment ℝ 0 (net.patch 3).right) :
    graph.curvature (fanNeighbor source (slit + 1)) + graph.curvature (fanNeighbor source slit) +
      2 * graph.curvature (opposite source) +
      2 * angle (net.patch 0).left (net.patch 0).right (net.patch 0).apex < π := by
  have contact_bound := net.first_cut_contact_angle_bound alternative threshold t positive upper contact
  have angle_sum : (net.patch 0).rightCorner +
      (graph.openingAngle (opposite source) slit 1 + graph.curvature (opposite source)) =
      π - angle (net.patch 0).pole (net.patch 0).left (net.patch 0).right +
        angle (net.patch 0).left (net.patch 0).right (net.patch 0).apex + graph.curvature (opposite source) := by
    have total := angle_add_angle_add_angle_eq_pi (net.patch 0).right
      (ne₁₃_of_not_collinear (net.patch 0).fan_noncollinear)
    rw [angle_comm (net.patch 0).right (net.patch 0).pole (net.patch 0).left, net.patch_fan_pole_angle] at total
    change _ + _ + (graph.openingAngle (opposite source) slit 1 - 0) = π at total
    have commute := angle_comm (net.patch 0).pole (net.patch 0).right (net.patch 0).left
    unfold DevelopedPatch.rightCorner
    linarith
  have strict_link := net.fan_left_corner_link 0
  simpa only [add_zero] using Curvature.finite_contact_budget contact_bound angle_sum strict_link

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
