import SixVertexUnfolding.Geometry.EdgeCutLocusStructure
import SixVertexUnfolding.Geometry.FaceCutLocusStructure

/-! Targets with three or more routes are locally finite everywhere except
possibly at the original vertices. This covers both face and edge interiors. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- Every nonvertex target has a neighborhood containing only finitely many three-or-more-route targets. -/
theorem nonvertex_junctions_locally_finite (a b : frontier P.body) (not_vertex : (b : Space) ∉ P.vertices) :
    ∃ U : Set Space, IsOpen U ∧ (b : Space) ∈ U ∧
      {c : frontier P.body | a ≠ c ∧ (c : Space) ∈ U ∧ 2 < Nat.card (P.geodesicFiber a c)}.Finite := by
  rcases P.nonvertex_incident_facets b.property not_vertex with ⟨F, _, unique⟩ | ⟨F, G, shared, target, _⟩
  · obtain ⟨U, openU, bU, covers⟩ := P.unique_face_neighborhood F unique
    refine ⟨U, openU, bU, (graph.face_junctions_finite small_faces a F).subset ?_⟩
    intro c hc
    exact ⟨hc.1, (covers _ ⟨hc.2.1, c.property⟩).2, hc.2.2⟩
  · obtain ⟨center, inside⟩ := P.solid
    obtain ⟨facets⟩ := P.exists_normalized_facets inside
    obtain ⟨chart⟩ := exists_edge_folding facets F G shared
    obtain ⟨patch⟩ := chart.exists_metric_patch shared target not_vertex
    exact ⟨patch.domain, patch.open_domain, patch.center_mem, patch.junctions_finite graph small_faces a⟩

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
