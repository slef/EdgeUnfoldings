import SixVertexUnfolding.Geometry.OctahedralCurvature
import SixVertexUnfolding.Geometry.FourRayClosedLink

/-! The strict closed-link inequality for the actual spatial angles of the six-vertex solid. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open OctahedralTriangles

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)

/-- The four incident directions generate the entire original vertex figure. -/
theorem fan_hull_eq_figure_hull (v : Fin 6) (figure : P.VertexFigure (graph.vertex v)) :
    convexHull ℝ (Set.range (graph.fanRay v figure)) = convexHull ℝ figure.points := by
  apply Set.Subset.antisymm
  · apply convexHull_mono
    rintro x ⟨i, rfl⟩
    exact ⟨graph.vertex (fanNeighbor v i),
      ⟨(graph.vertex (fanNeighbor v i)).property, graph.fan_neighbor_distinct v i⟩, rfl⟩
  · rw [← figure.corners_hull]
    exact convexHull_mono (graph.figure_corners_subset_fan v figure)

/-- The direction to any other original vertex belongs to the closed four-ray figure. -/
theorem vertex_direction_mem_fan (v : Fin 6) (figure : P.VertexFigure (graph.vertex v))
    (w : Fin 6) (different : w ≠ v) :
    figure.direction (graph.vertex w) ∈ convexHull ℝ (Set.range (graph.fanRay v figure)) := by
  rw [graph.fan_hull_eq_figure_hull]
  apply subset_convexHull ℝ _
  exact ⟨graph.vertex w, ⟨(graph.vertex w).property,
    fun same => different (graph.vertex.injective (Subtype.ext same))⟩, rfl⟩

/-- Transverse normalization preserves the angle between any two outgoing original-vertex rays. -/
theorem vertex_direction_angle (v : Fin 6) (figure : P.VertexFigure (graph.vertex v))
    (a b : Fin 6) (av : a ≠ v) (bv : b ≠ v) :
    InnerProductGeometry.angle (figure.direction (graph.vertex a)) (figure.direction (graph.vertex b)) =
      EuclideanGeometry.angle (graph.vertex a : Space) (graph.vertex v : Space) (graph.vertex b : Space) := by
  have a_ne : (graph.vertex a : Space) ≠ (graph.vertex v : Space) := fun same => av (graph.vertex.injective (Subtype.ext same))
  have b_ne : (graph.vertex b : Space) ≠ (graph.vertex v : Space) := fun same => bv (graph.vertex.injective (Subtype.ext same))
  rw [VertexFigure.direction, VertexFigure.direction,
    InnerProductGeometry.angle_smul_left_of_pos _ _ (inv_pos.mpr (figure.gap_pos (graph.vertex a).property a_ne)),
    InnerProductGeometry.angle_smul_right_of_pos _ _ (inv_pos.mpr (figure.gap_pos (graph.vertex b).property b_ne))]
  rfl

variable (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4)

/-- The supported fan's angular perimeter is exactly the actual incident face-angle sum. -/
theorem vertexFan_angle_sum (v : Fin 6) (figure : P.VertexFigure (graph.vertex v)) :
    (∑ i : Fin 4, InnerProductGeometry.angle ((graph.vertexFan v figure small_faces).ray i)
      ((graph.vertexFan v figure small_faces).ray (i + 1))) = graph.totalAngleAt v := by
  rw [graph.totalAngleAt_eq_fan_angles]
  apply Finset.sum_congr rfl
  intro i member
  rw [graph.vertexFan_ray, graph.vertexFan_ray, graph.fanRay_angle]

include small_faces in
/-- The closed-link bound applies even when the second ray points to the opposite, nonadjacent vertex. -/
theorem fan_vertex_link_bound (v : Fin 6) (i : Fin 4) (w : Fin 6) (different : w ≠ v) :
    2 * EuclideanGeometry.angle (graph.vertex (fanNeighbor v i) : Space)
      (graph.vertex v : Space) (graph.vertex w : Space) < graph.totalAngleAt v := by
  obtain ⟨normal, strict⟩ := P.vertex_strict_support (graph.vertex v).property
  let figure : P.VertexFigure (graph.vertex v) := ⟨normal, strict⟩
  have member : figure.direction (graph.vertex w) ∈
      convexHull ℝ (Set.range (graph.vertexFan v figure small_faces).ray) :=
    graph.vertex_direction_mem_fan v figure w different
  have bound := (graph.vertexFan v figure small_faces).closed_link_bound_from i member
  rw [graph.vertexFan_angle_sum] at bound
  change 2 * InnerProductGeometry.angle (figure.direction (graph.vertex (fanNeighbor v i)))
    (figure.direction (graph.vertex w)) < graph.totalAngleAt v at bound
  rwa [graph.vertex_direction_angle v figure _ _ (fanNeighbor_ne_source v i) different] at bound

include small_faces in
/-- A named incident original or auxiliary ray satisfies the same strict half-perimeter bound. -/
theorem vertex_link_bound (v a b : Fin 6) (av : a ≠ v) (bv : b ≠ v) (not_opposite : a ≠ opposite v) :
    2 * EuclideanGeometry.angle (graph.vertex a : Space) (graph.vertex v : Space) (graph.vertex b : Space) <
      graph.totalAngleAt v := by
  obtain ⟨i, rfl⟩ := fanNeighbor_exhaust v a av not_opposite
  exact graph.fan_vertex_link_bound small_faces v i b bv

include small_faces in
/-- Curvature notation for the geometric strict closed-link inequality. -/
theorem vertex_angle_lt_half_deficit (v a b : Fin 6) (av : a ≠ v) (bv : b ≠ v)
    (not_opposite : a ≠ opposite v) :
    2 * EuclideanGeometry.angle (graph.vertex a : Space) (graph.vertex v : Space) (graph.vertex b : Space) <
      2 * Real.pi - graph.curvature v := by
  have bound := graph.vertex_link_bound small_faces v a b av bv not_opposite
  simpa only [curvature, sub_sub_cancel] using bound

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
