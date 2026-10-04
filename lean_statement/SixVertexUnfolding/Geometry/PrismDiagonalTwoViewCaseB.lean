import SixVertexUnfolding.Geometry.PrismDiagonalUpperCaseB

/-! The two middle-angle sums add to one full turn. Hence at least one of
the two proved Case B views applies whenever both outer sums reach π. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Prism Prism.FaceLabel Real

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4}
variable (prism_kind : graph.kind = .prismDiagonal)
include prism_kind

/-- The complementary middle fans consist of exactly the angles of triangles C and E. -/
theorem prism_middle_view_sum :
    (graph.prismAngle small_faces C 0 +
      (graph.prismAngle small_faces C 1 + graph.prismAngle small_faces E 1)) +
    (graph.prismAngle small_faces E 4 +
      (graph.prismAngle small_faces E 3 + graph.prismAngle small_faces C 3)) = 2 * π := by
  have triangleC := graph.prismAngle_sum small_faces prism_kind C
  have triangleE := graph.prismAngle_sum small_faces prism_kind E
  simp [Fin.sum_univ_succ, graph.prismAngle_zero small_faces prism_kind, faceVertices] at triangleC triangleE
  linarith

/-- If each cap's base curvatures cover its apex angle, the fallback is an edge unfolding.
The two-view choice and all fifteen whole-face comparisons are proved here. -/
theorem prismDiagonal_hasEdgeUnfolding_of_wide_caps
    (lower_wide : graph.prismAngle small_faces A 2 ≤
      graph.curvature (vertexLabel 0) + graph.curvature (vertexLabel 1))
    (upper_wide : graph.prismAngle small_faces F 5 ≤
      graph.curvature (vertexLabel 3) + graph.curvature (vertexLabel 4)) : P.HasEdgeUnfolding := by
  have triangleA := graph.prismAngle_sum small_faces prism_kind A
  have triangleF := graph.prismAngle_sum small_faces prism_kind F
  simp [Fin.sum_univ_succ, graph.prismAngle_zero small_faces prism_kind, faceVertices] at triangleA triangleF
  have middle := graph.prism_middle_view_sum (small_faces := small_faces) prism_kind
  by_cases lower : π ≤ graph.prismAngle small_faces C 0 +
      (graph.prismAngle small_faces C 1 + graph.prismAngle small_faces E 1)
  · exact graph.prismDiagonal_hasEdgeUnfolding_of_lower_caseB prism_kind (by linarith) lower
  · exact graph.prismDiagonal_hasEdgeUnfolding_of_upper_caseB prism_kind (by linarith) (by linarith)

/-- Only a narrow cap can remain after the completed two-view Case B argument. -/
theorem prismDiagonal_unfolding_or_narrow_cap :
    P.HasEdgeUnfolding ∨
      graph.curvature (vertexLabel 0) + graph.curvature (vertexLabel 1) <
        graph.prismAngle small_faces A 2 ∨
      graph.curvature (vertexLabel 3) + graph.curvature (vertexLabel 4) <
        graph.prismAngle small_faces F 5 := by
  by_cases lower : graph.prismAngle small_faces A 2 ≤
      graph.curvature (vertexLabel 0) + graph.curvature (vertexLabel 1)
  · by_cases upper : graph.prismAngle small_faces F 5 ≤
        graph.curvature (vertexLabel 3) + graph.curvature (vertexLabel 4)
    · exact Or.inl (graph.prismDiagonal_hasEdgeUnfolding_of_wide_caps prism_kind lower upper)
    · exact Or.inr (Or.inr (lt_of_not_ge upper))
  · exact Or.inr (Or.inl (lt_of_not_ge lower))

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
