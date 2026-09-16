import SixVertexUnfolding.Geometry.OctahedralHalfFan
import SixVertexUnfolding.Geometry.OutwardPatch
import SixVertexUnfolding.Geometry.TriangleAngles
import SixVertexUnfolding.Geometry.TriangleNondegeneracy

/-! One developed fan triangle and its attached petal, using the five original lengths. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open OctahedralTriangles EuclideanGeometry Real

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)

/-- A rigid two-triangle patch, with the petal unfolded outward across its equator hinge. -/
structure DevelopedPatch (source : Fin 6) (sector : Fin 4) where
  pole : Plane
  left : Plane
  right : Plane
  apex : Plane
  hinge_length : dist left right = dist (graph.vertex (fanNeighbor source sector) : Space)
    (graph.vertex (fanNeighbor source (sector + 1)))
  fan_left : dist pole left = dist (graph.vertex (opposite source) : Space) (graph.vertex (fanNeighbor source sector))
  fan_right : dist pole right = dist (graph.vertex (opposite source) : Space) (graph.vertex (fanNeighbor source (sector + 1)))
  petal_left : dist apex left = dist (graph.vertex source : Space) (graph.vertex (fanNeighbor source sector))
  petal_right : dist apex right = dist (graph.vertex source : Space) (graph.vertex (fanNeighbor source (sector + 1)))
  outward : OppositeHingeSides left right pole apex

namespace DevelopedPatch

variable {graph} {source : Fin 6} {sector : Fin 4} (patch : graph.DevelopedPatch source sector)

/-- The closed hull contains both triangles of the patch. -/
def hull : Set Plane := convexHull ℝ ({patch.pole, patch.left, patch.right, patch.apex} : Set Plane)

theorem equator_distinct : fanNeighbor source sector ≠ fanNeighbor source (sector + 1) :=
  (fanNeighbor_injective source).ne ((by decide : ∀ i : Fin 4, i ≠ i + 1) sector)

/-- Neither rigid fan triangle collapses in the plane. -/
theorem fan_noncollinear : ¬ Collinear ℝ ({patch.left, patch.right, patch.pole} : Set Plane) := by
  apply P.placed_triangle_noncollinear
    (graph.vertex (fanNeighbor source sector)) (graph.vertex (fanNeighbor source (sector + 1)))
    (graph.vertex (opposite source))
  · exact graph.vertex.injective.ne equator_distinct
  · exact graph.vertex.injective.ne ((by decide : ∀ s i, fanNeighbor s i ≠ opposite s) source sector)
  · exact graph.vertex.injective.ne ((by decide : ∀ s i, fanNeighbor s i ≠ opposite s) source (sector + 1))
  · exact patch.hinge_length
  · simpa only [dist_comm] using patch.fan_left
  · simpa only [dist_comm] using patch.fan_right

/-- Opening this hinge cannot shorten the distance between the pole and the copied source. -/
theorem pole_distance_ge : dist (graph.vertex (opposite source) : Space) (graph.vertex source) ≤
    dist patch.pole patch.apex := by
  apply two_triangles_distance_ge (graph.vertex (fanNeighbor source sector))
    (graph.vertex (fanNeighbor source (sector + 1))) _ _ patch.left patch.right patch.pole patch.apex
  · exact fun same => equator_distinct (graph.vertex.injective (Subtype.ext same))
  · exact patch.hinge_length
  · simpa only [dist_comm] using patch.fan_left
  · simpa only [dist_comm] using patch.fan_right
  · simpa only [dist_comm] using patch.petal_left
  · simpa only [dist_comm] using patch.petal_right
  · exact patch.outward

variable (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include small_faces in
/-- All three pairs of outgoing corner rays satisfy the strict half-fan estimate. -/
theorem corner_angle_bounds
    (alternative : π ≤ graph.curvature source ∨ graph.curvature (opposite source) ≤ π) :
    2 * angle patch.left patch.pole patch.right < graph.totalAngleAt (opposite source) ∧
    2 * angle patch.left patch.pole patch.apex < graph.totalAngleAt (opposite source) ∧
    2 * angle patch.right patch.pole patch.apex < graph.totalAngleAt (opposite source) := by
  refine ⟨?_, graph.developed_petal_angle_bound small_faces source sector _ _ _
    patch.fan_left patch.petal_left patch.pole_distance_ge alternative,
    graph.developed_petal_angle_bound small_faces source (sector + 1) _ _ _
      patch.fan_right patch.petal_right patch.pole_distance_ge alternative⟩
  rw [triangle_angle_of_distances _ _ _ _ _ _ patch.fan_left patch.fan_right patch.hinge_length]
  apply graph.vertex_link_bound small_faces
  · exact (by decide : ∀ s i, fanNeighbor s i ≠ opposite s) source sector
  · exact (by decide : ∀ s i, fanNeighbor s i ≠ opposite s) source (sector + 1)
  · rw [opposite_opposite]
    exact fanNeighbor_ne_source source sector

end DevelopedPatch
end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
