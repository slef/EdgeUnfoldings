import SixVertexUnfolding.Geometry.OctahedralAngles
import SixVertexUnfolding.OctahedralAngleIncidence
import SixVertexUnfolding.Geometry.OctahedralVertexFigure
import SixVertexUnfolding.Geometry.FourRayPerimeter

/-! Strict positivity of curvature at every genuine vertex of the four canonical surfaces. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open OctahedralTriangles

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)

/-- The incident triangle angles are precisely the four successive angles of the cyclic fan. -/
theorem totalAngleAt_eq_fan_angles (v : Fin 6) : graph.totalAngleAt v =
    ∑ i : Fin 4, EuclideanGeometry.angle (graph.vertex (fanNeighbor v i) : Space)
      (graph.vertex v : Space) (graph.vertex (fanNeighbor v (i + 1)) : Space) := by
  exact angle_incidence
    (fun a b c => EuclideanGeometry.angle (graph.vertex a : Space) (graph.vertex b : Space) (graph.vertex c : Space))
    (fun a b c => EuclideanGeometry.angle_comm _ _ _) v

/-- Cutting rays by a positive transverse height preserves each incident spatial angle. -/
theorem fanRay_angle (v : Fin 6) (figure : P.VertexFigure (graph.vertex v)) (i : Fin 4) :
    InnerProductGeometry.angle (graph.fanRay v figure i) (graph.fanRay v figure (i + 1)) =
      EuclideanGeometry.angle (graph.vertex (fanNeighbor v i) : Space)
        (graph.vertex v : Space) (graph.vertex (fanNeighbor v (i + 1)) : Space) := by
  have first := figure.gap_pos (graph.vertex (fanNeighbor v i)).property (graph.fan_neighbor_distinct v i)
  have second := figure.gap_pos (graph.vertex (fanNeighbor v (i + 1))).property
    (graph.fan_neighbor_distinct v (i + 1))
  rw [fanRay, fanRay, VertexFigure.direction, VertexFigure.direction,
    InnerProductGeometry.angle_smul_left_of_pos _ _ (inv_pos.mpr first),
    InnerProductGeometry.angle_smul_right_of_pos _ _ (inv_pos.mpr second)]
  rfl

/-- Convex supporting facets make the actual incident angle sum strictly less than a full turn. -/
theorem totalAngleAt_lt_two_pi
    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4) (v : Fin 6) :
    graph.totalAngleAt v < 2 * Real.pi := by
  obtain ⟨normal, strict⟩ := P.vertex_strict_support (graph.vertex v).property
  let figure : P.VertexFigure (graph.vertex v) := ⟨normal, strict⟩
  have bound := (graph.vertexFan v figure small_faces).sum_angles_lt_two_pi
  have angles : graph.totalAngleAt v = ∑ i : Fin 4,
      InnerProductGeometry.angle ((graph.vertexFan v figure small_faces).ray i)
        ((graph.vertexFan v figure small_faces).ray (i + 1)) := by
    rw [graph.totalAngleAt_eq_fan_angles]
    apply Finset.sum_congr rfl
    intro i member
    rw [graph.vertexFan_ray, graph.vertexFan_ray, graph.fanRay_angle]
  rwa [← angles] at bound

/-- Every genuine vertex has strictly positive curvature, even with flat auxiliary hinges. -/
theorem curvature_pos
    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4) (v : Fin 6) : 0 < graph.curvature v := by
  have bound := graph.totalAngleAt_lt_two_pi small_faces v
  unfold curvature
  linarith

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
