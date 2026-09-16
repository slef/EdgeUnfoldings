import SixVertexUnfolding

namespace SixVertexUnfolding

-- The original target, with its definitions unchanged in Definitions.lean.
-- The universal-source star case is proved; only the prism with a diagonal remains.
-- See README.md for the proved dependencies. This is the only project sorry.
theorem every_convex_polyhedron_with_at_most_six_vertices
    (P : ConvexPolyhedron) (at_most_six : P.vertices.card ≤ 6) :
    P.HasEdgeUnfolding := by
  rcases unfolding_or_universal_or_prismDiagonal P at_most_six with unfolded | remaining
  · exact unfolded
  · rcases remaining with ⟨six, small_faces, universal | ⟨graph, kind⟩⟩
    · obtain ⟨source, universal⟩ := universal
      exact ConvexPolyhedron.universal_star_has_edge_unfolding six small_faces source universal
    · sorry

end SixVertexUnfolding
