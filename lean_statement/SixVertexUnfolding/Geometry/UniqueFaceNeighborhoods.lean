import SixVertexUnfolding.Geometry.NonvertexFacetNeighborhoods

/-! A point belonging to only one original facet has a surface neighborhood
with that same unique facet. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

theorem unique_face_neighborhood (P : ConvexPolyhedron) (F : P.Face) {b : Space}
    (unique : ∀ G : P.Face, b ∈ G.val → G = F) :
    ∃ U : Set Space, IsOpen U ∧ b ∈ U ∧
      ∀ x ∈ U ∩ frontier P.body, x ∈ F.val ∧ ∀ G : P.Face, x ∈ G.val → G = F := by
  obtain ⟨U, openU, bU, incident⟩ := P.incident_facets_neighborhood b
  refine ⟨U, openU, bU, ?_⟩
  intro x hx
  have only (G : P.Face) (hxG : x ∈ G.val) : G = F := unique G (incident x hx.1 G hxG)
  obtain ⟨G, hxG⟩ := P.boundary_point_in_face hx.2
  exact ⟨only G hxG ▸ hxG, only⟩

end SixVertexUnfolding.ConvexPolyhedron
