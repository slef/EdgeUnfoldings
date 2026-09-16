import SixVertexUnfolding.PrismFlower
import SixVertexUnfolding.Geometry.DomeComplete

/-! Every ordinary convex triangular prism unfolds from a whole quadrilateral base. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

/-- All geometric realizations of the ordinary prism graph have an original-edge unfolding. -/
theorem hasEdgeUnfolding_of_prism {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4)
    (kind : graph.kind = .prism) : P.HasEdgeUnfolding :=
  (graph.prismDome small_faces kind).hasEdgeUnfolding

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
