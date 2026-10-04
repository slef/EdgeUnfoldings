import SixVertexUnfolding.Geometry.PrismDiagonalHighCaps

/-! The cap rule covers every prism with a diagonal whose vertex curvatures
are all at most π. Remaining shapes necessarily have a sharper vertex. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Prism Real

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
variable (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4)
variable (prism_kind : graph.kind = .prismDiagonal)
include small_faces prism_kind

/-- With no curvature above π, each triangular cap must carry at least π. -/
theorem prismDiagonal_hasEdgeUnfolding_of_no_sharp_vertices
    (bounded : ∀ i, graph.curvature i ≤ π) : P.HasEdgeUnfolding := by
  have total := graph.prism_cap_curvature_sum
  have lower_bound : graph.prismLowerCapCurvature ≤ 3 * π := by
    unfold prismLowerCapCurvature
    linarith [bounded (vertexLabel 0), bounded (vertexLabel 1), bounded (vertexLabel 2)]
  have upper_bound : graph.prismUpperCapCurvature ≤ 3 * π := by
    unfold prismUpperCapCurvature
    linarith [bounded (vertexLabel 3), bounded (vertexLabel 4), bounded (vertexLabel 5)]
  exact graph.prismDiagonal_hasEdgeUnfolding_of_high_caps (small_faces := small_faces)
    prism_kind (by linarith) (by linarith)

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
