import SixVertexUnfolding.Geometry.PrismDiagonalLowerCaseB
import SixVertexUnfolding.Geometry.ReverseCornerFans

/-! The second Case B view uses the same cap-frame argument, reading the
upper fans backwards. No reflection or placement hypothesis is added. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Prism Prism.FaceLabel Real

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4}
variable (prism_kind : graph.kind = .prismDiagonal)
include prism_kind

/-- The upper view's cut-ray directions, reading the base from 4 to 3. -/
theorem prism_upper_base_angles :
    graph.prismAngle small_faces F 4 + graph.curvature (vertexLabel 4) =
      2 * π - (graph.prismAngle small_faces E 4 + graph.prismAngle small_faces D 4) ∧
    graph.prismAngle small_faces F 3 + graph.curvature (vertexLabel 3) =
      2 * π - (graph.prismAngle small_faces E 3 + graph.prismAngle small_faces C 3 +
        graph.prismAngle small_faces B 3) := by
  constructor <;> rw [graph.prism_curvature_eq small_faces prism_kind, sum_faces] <;>
    simp [graph.prismAngle_zero small_faces prism_kind, faceVertices] <;> ring

/-- The upper view separates the entire quadrilaterals under the Case B angle bounds. -/
theorem PrismFallbackDevelopment.upper_caseB
    (net : graph.PrismFallbackDevelopment small_faces)
    (outer_sum : π ≤ (graph.prismAngle small_faces F 4 + graph.curvature (vertexLabel 4)) +
      (graph.prismAngle small_faces F 3 + graph.curvature (vertexLabel 3)))
    (fan_sum : π ≤ graph.prismAngle small_faces E 4 +
      (graph.prismAngle small_faces E 3 + graph.prismAngle small_faces C 3)) :
    Disjoint (net.place B '' (graph.prismDiagonalFace small_faces B).val)
      (net.place D '' (graph.prismDiagonalFace small_faces D).val) := by
  let left := (net.shortVertexFan prism_kind 1).reverse
  let right := (net.vertexFan prism_kind 1).reverse
  have right_center : right.center = left.ray 1 := (net.fan_positions prism_kind 1 2).1
  have common_apex : right.ray 0 = left.ray 0 := rfl
  have left_center : right.ray 1 = left.center := rfl
  have directions := graph.prism_upper_base_angles (small_faces := small_faces) prism_kind
  rw [directions.1, directions.2] at outer_sum
  have separated := two_fan_base_cones_disjoint left right right_center common_apex left_center
    (by dsimp only [left]; rw [ThreeTriangleChain.reverse_angle_sum]; exact net.shortVertexFan_one_turn prism_kind 1)
    (by dsimp only [right]; rw [FourTriangleChain.reverse_angle_sum]; exact net.vertexFan_one_turn prism_kind 1)
    (by simpa [left, right, net.shortVertexFan_corner prism_kind,
      net.vertexFan_corner prism_kind, shortFanFace, shortFanCenter, fanFace, fanCenter,
      Fin.rev] using outer_sum)
    (by simpa [left, right, net.shortVertexFan_corner prism_kind,
      net.vertexFan_corner prism_kind, shortFanFace, shortFanCenter, fanFace, fanCenter,
      Fin.rev] using fan_sum)
  have original_cones : Disjoint ((net.shortVertexFan prism_kind 1).cornerCone 0)
      ((net.vertexFan prism_kind 1).cornerCone 0) := by
    simpa [left, right, Fin.rev] using separated
  exact (original_cones.mono (net.face_subset_shortVertexFan_cone prism_kind 1 0)
    (net.face_subset_vertexFan_cone prism_kind 1 0)).symm

/-- The upper Case B region gives an actual public edge unfolding. -/
theorem prismDiagonal_hasEdgeUnfolding_of_upper_caseB
    (outer_sum : π ≤ (graph.prismAngle small_faces F 4 + graph.curvature (vertexLabel 4)) +
      (graph.prismAngle small_faces F 3 + graph.curvature (vertexLabel 3)))
    (fan_sum : π ≤ graph.prismAngle small_faces E 4 +
      (graph.prismAngle small_faces E 3 + graph.prismAngle small_faces C 3)) : P.HasEdgeUnfolding := by
  obtain ⟨net, other_pairs⟩ := graph.exists_prism_fallback_safe_except_quadrilaterals
    (small_faces := small_faces) prism_kind
  exact net.hasEdgeUnfolding_of_quadrilaterals prism_kind other_pairs
    ((net.upper_caseB prism_kind outer_sum fan_sum).mono interior_subset interior_subset)

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
