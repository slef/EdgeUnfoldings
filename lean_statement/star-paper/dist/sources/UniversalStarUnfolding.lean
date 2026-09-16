import SixVertexUnfolding.Geometry.UniversalStarEmbedding
import SixVertexUnfolding.Geometry.UniversalStarInteriors
import SixVertexUnfolding.Reduction

/-! The completed universal-source star development yields an unfolding
of the original whole faces, using the unchanged public definition. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- The universal-source star gives an edge unfolding in the remaining small-face family. -/
theorem universal_star_has_edge_unfolding {P : ConvexPolyhedron} (six : P.vertices.card = 6)
    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4)
    (source : P.Vertex) (universal : ∀ v : P.Vertex, v ≠ source → P.edgeGraph.Adj source v) :
    P.HasEdgeUnfolding := by
  let a : frontier P.body := ⟨source, P.vertex_mem_frontier source.property⟩
  have cofacial := universal_source_cofacial a source rfl universal
  obtain ⟨develop, embedding, _, _, _, locally_isometric⟩ :=
    universal_star_embedding six small_faces a source rfl universal
  exact edge_unfolding_of_star_development develop embedding.injective locally_isometric
    (small_cofacial_uncut_surface_pathConnected (show P.vertices.card ≤ 6 by omega)
      small_faces a cofacial).isConnected.isPreconnected
    (P.universal_star_face_interiors_uncut a source rfl universal)

/-- With at most six vertices, a universal vertex always gives an edge unfolding.
The earlier reduction handles smaller solids and faces with more than four vertices. -/
theorem hasEdgeUnfolding_of_universal_vertex {P : ConvexPolyhedron}
    (at_most_six : P.vertices.card ≤ 6) (source : P.Vertex)
    (universal : ∀ v : P.Vertex, v ≠ source → P.edgeGraph.Adj source v) :
    P.HasEdgeUnfolding := by
  rcases unfolding_or_remaining_cases P at_most_six with unfolded | ⟨six, small_faces⟩
  · exact unfolded
  · exact universal_star_has_edge_unfolding six small_faces source universal

end SixVertexUnfolding.ConvexPolyhedron
