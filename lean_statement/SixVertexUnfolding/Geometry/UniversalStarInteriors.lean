import SixVertexUnfolding.Geometry.FaceInteriorUniqueness
import SixVertexUnfolding.Geometry.StarEdgeAssembly

/-! At a universal original vertex, every straight star cut is an
original edge. Hence no original face interior is cut. This discharges
the face-interior condition in the star-to-edge assembly theorem. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- The original face interiors survive all star cuts from a universal vertex. -/
theorem universal_star_face_interiors_uncut (P : ConvexPolyhedron)
    (a : frontier P.body) (source : P.Vertex) (at_source : (a : Space) = (source : Space))
    (universal : ∀ v : P.Vertex, v ≠ source → P.edgeGraph.Adj source v)
    (F : P.Face) (x : Space) (xF : x ∈ F.val)
    (inside : P.faceCoordinates F x ∈ interior (P.faceCoordinates F '' F.val)) :
    (⟨x, F.subset_frontier xF⟩ : frontier P.body) ∉ P.starCuts a := by
  rintro ⟨v, on_cut⟩
  have on_edge : ∃ A B : P.Face, P.ShareEdge A B ∧ x ∈ A.val ∩ B.val := by
    by_cases same : v = source
    · have at_vertex : x = (source : Space) := by
        simpa only [at_source, same, segment_same, mem_singleton_iff] using on_cut
      obtain ⟨w, original, different⟩ := Finset.exists_mem_ne
        (show 1 < P.vertices.card by have := P.four_le_vertex_count; omega) (source : Space)
      have different_vertex : (⟨w, original⟩ : P.Vertex) ≠ source :=
        fun equal => different (congrArg Subtype.val equal)
      obtain ⟨_, A, B, shared, edge⟩ := universal ⟨w, original⟩ different_vertex
      refine ⟨A, B, shared, ?_⟩
      rw [edge, at_vertex]
      exact left_mem_segment ℝ _ _
    · obtain ⟨_, A, B, shared, edge⟩ := universal v same
      refine ⟨A, B, shared, ?_⟩
      rw [edge]
      simpa only [at_source] using on_cut
  obtain ⟨A, B, shared, xA, xB⟩ := on_edge
  have first := F.unique_of_placed_interior A (P.faceCoordinates F) (P.faceCoordinates_rigid F) xF inside xA
  have second := F.unique_of_placed_interior B (P.faceCoordinates F) (P.faceCoordinates_rigid F) xF inside xB
  have same : A = B := first.symm.trans second
  apply A.shareEdge_irrefl
  simpa only [← same] using shared

end SixVertexUnfolding.ConvexPolyhedron
