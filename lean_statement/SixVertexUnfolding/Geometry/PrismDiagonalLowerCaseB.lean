import SixVertexUnfolding.Geometry.PrismDiagonalOnePair
import SixVertexUnfolding.Geometry.TwoFanBaseSeparation

/-! The lower-cap Case B comparison applies to the actual fallback polygons,
not merely to an abstract configuration of rays. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Prism Prism.FaceLabel Real

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4}
variable (prism_kind : graph.kind = .prismDiagonal)
include prism_kind

/-- Curvature gives the two cut-ray directions measured from the lower cap's base. -/
theorem prism_lower_base_angles :
    graph.prismAngle small_faces A 0 + graph.curvature (vertexLabel 0) =
      2 * π - (graph.prismAngle small_faces C 0 + graph.prismAngle small_faces B 0) ∧
    graph.prismAngle small_faces A 1 + graph.curvature (vertexLabel 1) =
      2 * π - (graph.prismAngle small_faces C 1 + graph.prismAngle small_faces E 1 +
        graph.prismAngle small_faces D 1) := by
  constructor <;> rw [graph.prism_curvature_eq small_faces prism_kind, sum_faces] <;>
    simp [graph.prismAngle_zero small_faces prism_kind, faceVertices] <;> ring

/-- The lower view separates the entire quadrilaterals when both angle sums reach π. -/
theorem PrismFallbackDevelopment.lower_caseB
    (net : graph.PrismFallbackDevelopment small_faces)
    (outer_sum : π ≤ (graph.prismAngle small_faces A 0 + graph.curvature (vertexLabel 0)) +
      (graph.prismAngle small_faces A 1 + graph.curvature (vertexLabel 1)))
    (fan_sum : π ≤ graph.prismAngle small_faces C 0 +
      (graph.prismAngle small_faces C 1 + graph.prismAngle small_faces E 1)) :
    Disjoint (net.place B '' (graph.prismDiagonalFace small_faces B).val)
      (net.place D '' (graph.prismDiagonalFace small_faces D).val) := by
  let left := net.shortVertexFan prism_kind 0
  let right := net.vertexFan prism_kind 0
  have right_center : right.center = left.ray 1 := (net.fan_positions prism_kind 0 0).1
  have common_apex : right.ray 0 = left.ray 0 := rfl
  have left_center : right.ray 1 = left.center := (net.short_fan_positions prism_kind 0 0).1.symm
  have directions := graph.prism_lower_base_angles (small_faces := small_faces) prism_kind
  rw [directions.1, directions.2] at outer_sum
  have separated := two_fan_base_cones_disjoint left right right_center common_apex left_center
    (net.shortVertexFan_one_turn prism_kind 0) (net.vertexFan_one_turn prism_kind 0)
    (by simpa only [left, right, net.shortVertexFan_corner prism_kind,
      net.vertexFan_corner prism_kind, shortFanFace, shortFanCenter, fanFace, fanCenter,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three] using outer_sum)
    (by simpa only [left, right, net.shortVertexFan_corner prism_kind,
      net.vertexFan_corner prism_kind, shortFanFace, shortFanCenter, fanFace, fanCenter,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] using fan_sum)
  exact separated.mono (net.face_subset_shortVertexFan_cone prism_kind 0 2)
    (net.face_subset_vertexFan_cone prism_kind 0 3)

/-- This geometric region now gives an actual public edge unfolding. -/
theorem prismDiagonal_hasEdgeUnfolding_of_lower_caseB
    (outer_sum : π ≤ (graph.prismAngle small_faces A 0 + graph.curvature (vertexLabel 0)) +
      (graph.prismAngle small_faces A 1 + graph.curvature (vertexLabel 1)))
    (fan_sum : π ≤ graph.prismAngle small_faces C 0 +
      (graph.prismAngle small_faces C 1 + graph.prismAngle small_faces E 1)) : P.HasEdgeUnfolding := by
  obtain ⟨net, other_pairs⟩ := graph.exists_prism_fallback_safe_except_quadrilaterals
    (small_faces := small_faces) prism_kind
  exact net.hasEdgeUnfolding_of_quadrilaterals prism_kind other_pairs
    ((net.lower_caseB prism_kind outer_sum fan_sum).mono interior_subset interior_subset)

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
