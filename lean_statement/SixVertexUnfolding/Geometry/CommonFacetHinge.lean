import SixVertexUnfolding.Geometry.CommonFacetVertices

/-! Two shared original vertices identify the whole original hinge of distinct facets. -/

namespace SixVertexUnfolding.ConvexPolyhedron.Face

variable {P : ConvexPolyhedron} (F G : P.Face)

theorem intersection_eq_segment_of_common_vertices (different : F ≠ G) (a b : P.Vertex) (ab : a ≠ b)
    (aF : (a : Space) ∈ F.val) (bF : (b : Space) ∈ F.val)
    (aG : (a : Space) ∈ G.val) (bG : (b : Space) ∈ G.val) :
    F.val ∩ G.val = segment ℝ (a : Space) b := by
  obtain ⟨_, H, K, shared, segment_eq⟩ := F.adjacent_of_common_vertices G different a b ab aF bF aG bG
  have first := H.facets_containing_shared_edge K shared F (by
    rw [segment_eq]
    exact F.convex.segment_subset aF bF)
  have second := H.facets_containing_shared_edge K shared G (by
    rw [segment_eq]
    exact G.convex.segment_subset aG bG)
  rcases first with rfl | rfl <;> rcases second with rfl | rfl
  · exact (different rfl).elim
  · exact segment_eq
  · simpa only [Set.inter_comm] using segment_eq
  · exact (different rfl).elim

end SixVertexUnfolding.ConvexPolyhedron.Face
