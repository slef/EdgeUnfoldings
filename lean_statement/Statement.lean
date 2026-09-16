import SixVertexUnfolding

namespace SixVertexUnfolding

-- The original target, with its definitions unchanged in Definitions.lean.
-- The remaining cases are universal vertices and the prism with a diagonal.
-- See README.md for the proved dependencies. This is the only project sorry.
theorem every_convex_polyhedron_with_at_most_six_vertices
    (P : ConvexPolyhedron) (at_most_six : P.vertices.card ≤ 6) :
    P.HasEdgeUnfolding := by
  rcases unfolding_or_universal_or_prismDiagonal P at_most_six with unfolded | remaining
  · exact unfolded
  · sorry

end SixVertexUnfolding
