import SixVertexUnfolding.Geometry.UniversalVertexCycle
import SixVertexUnfolding.Geometry.FiveCycleOrder

/-! A concrete cyclic numbering of the five neighboring vertices and
the five actual triangular faces incident to a universal source. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- Consecutive vertices in the cyclic order form an actual triangular face with the source. -/
theorem universal_vertex_face_order (P : ConvexPolyhedron) (size : P.vertices.card = 6)
    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4)
    (source : P.Vertex) (universal : ∀ v : P.Vertex, v ≠ source → P.edgeGraph.Adj source v) :
    ∃ order : Fin 5 ≃ {v : P.Vertex // v ≠ source}, ∃ faces : Fin 5 → P.Face,
      ∀ i : Fin 5, (faces i).val ∩ (P.vertices : Set Space) =
        {(source : Space), ((order i).val : Space), ((order (i + 1)).val : Space)} := by
  classical
  have five : Fintype.card {v : P.Vertex // v ≠ source} = 5 :=
    Nat.card_eq_fintype_card.symm.trans (P.six_vertex_link_card size source)
  obtain ⟨b⟩ := Fintype.card_pos_iff.mp (show 0 < Fintype.card {v : P.Vertex // v ≠ source} by omega)
  obtain ⟨p, cycle, covers⟩ := P.universal_vertex_link_cycle size small_faces source universal b
  obtain ⟨order, consecutive⟩ := five_cycle_order (P.vertexLink source) five p cycle covers
  have face_exists (i : Fin 5) : ∃ F : P.Face, F.val ∩ (P.vertices : Set Space) =
      {(source : Space), ((order i).val : Space), ((order (i + 1)).val : Space)} := by
    obtain ⟨different, F, sourceF, firstF, nextF⟩ := consecutive i
    obtain ⟨c, _, _, vertices⟩ := F.exists_third_vertex
      (P.universal_vertex_facets_triangular small_faces source universal F sourceF)
      source (order i).val (order i).property.symm sourceF firstF
    have next : ((order (i + 1)).val : Space) ∈ F.val ∩ (P.vertices : Set Space) :=
      ⟨nextF, (order (i + 1)).val.property⟩
    rw [vertices] at next
    have next_source : ((order (i + 1)).val : Space) ≠ source :=
      fun same => (order (i + 1)).property (Subtype.ext same)
    have next_first : ((order (i + 1)).val : Space) ≠ ((order i).val : Space) :=
      fun same => different (Subtype.ext (Subtype.ext same.symm))
    have next_c : ((order (i + 1)).val : Space) = c :=
      (next.resolve_left next_source).resolve_left next_first
    exact ⟨F, by rw [vertices, ← next_c]⟩
  choose faces vertices using face_exists
  exact ⟨order, faces, vertices⟩

end SixVertexUnfolding.ConvexPolyhedron
