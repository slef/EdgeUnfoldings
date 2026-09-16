import SixVertexUnfolding.Geometry.OctahedralPatch

/-! Nondegeneracy and the four equator-corner angles of a developed two-triangle patch. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.DevelopedPatch

open OctahedralTriangles EuclideanGeometry

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph} {source : Fin 6} {sector : Fin 4}
variable (patch : graph.DevelopedPatch source sector)

theorem petal_noncollinear : ¬ Collinear ℝ ({patch.left, patch.right, patch.apex} : Set Plane) := by
  apply P.placed_triangle_noncollinear
    (graph.vertex (fanNeighbor source sector)) (graph.vertex (fanNeighbor source (sector + 1)))
    (graph.vertex source)
  · exact graph.vertex.injective.ne equator_distinct
  · exact graph.vertex.injective.ne (fanNeighbor_ne_source source sector)
  · exact graph.vertex.injective.ne (fanNeighbor_ne_source source (sector + 1))
  · exact patch.hinge_length
  · simpa only [dist_comm] using patch.petal_left
  · simpa only [dist_comm] using patch.petal_right

theorem fan_angle_at_left : angle patch.pole patch.left patch.right =
    angle (graph.vertex (opposite source) : Space) (graph.vertex (fanNeighbor source sector))
      (graph.vertex (fanNeighbor source (sector + 1))) := by
  apply triangle_angle_of_distances
  · simpa only [dist_comm] using patch.fan_left
  · exact patch.hinge_length
  · exact patch.fan_right

theorem fan_angle_at_right : angle patch.left patch.right patch.pole =
    angle (graph.vertex (fanNeighbor source sector) : Space) (graph.vertex (fanNeighbor source (sector + 1)))
      (graph.vertex (opposite source)) := by
  apply triangle_angle_of_distances
  · simpa only [dist_comm] using patch.hinge_length
  · simpa only [dist_comm] using patch.fan_right
  · simpa only [dist_comm] using patch.fan_left

theorem petal_angle_at_left : angle patch.right patch.left patch.apex =
    angle (graph.vertex (fanNeighbor source (sector + 1)) : Space) (graph.vertex (fanNeighbor source sector))
      (graph.vertex source) := by
  apply triangle_angle_of_distances
  · exact patch.hinge_length
  · simpa only [dist_comm] using patch.petal_left
  · simpa only [dist_comm] using patch.petal_right

theorem petal_angle_at_right : angle patch.apex patch.right patch.left =
    angle (graph.vertex source : Space) (graph.vertex (fanNeighbor source (sector + 1)))
      (graph.vertex (fanNeighbor source sector)) := by
  apply triangle_angle_of_distances
  · simpa only [dist_comm] using patch.petal_right
  · simpa only [dist_comm] using patch.hinge_length
  · exact patch.petal_left

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.DevelopedPatch
