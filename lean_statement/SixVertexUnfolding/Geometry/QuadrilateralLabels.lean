import SixVertexUnfolding.Geometry.FacetLabels

/-! A whole quadrilateral facet gives an induced four-cycle on its original vertex labels. -/

namespace SixVertexUnfolding.ConvexPolyhedron.Face

open scoped Classical

variable {P : ConvexPolyhedron} (index : Fin 6 ≃ P.Vertex) (F : P.Face)

/-- Each original corner of a quadrilateral has exactly two neighbors inside that facet. -/
theorem quadrilateral_label_neighbors (four : (F.val ∩ (P.vertices : Set Space)).ncard = 4)
    (a : Fin 6) (aF : a ∈ F.vertexLabels index) :
    ((F.vertexLabels index).filter (fun b => P.edgeGraph.Adj (index a) (index b))).card = 2 := by
  classical
  obtain ⟨Q⟩ := F.exists_quadrilateral four
  let label (i : Fin 4) : Fin 6 := index.symm (Q.corner i)
  have label_injective : Function.Injective label := index.symm.injective.comp Q.distinct
  have label_vertex (i : Fin 4) : index (label i) = Q.corner i := index.apply_symm_apply _
  have corner_of_member (b : Fin 6) (bF : b ∈ F.vertexLabels index) : ∃ i, label i = b := by
    have member : (index b : Space) ∈ F.val ∩ (P.vertices : Set Space) :=
      ⟨(F.mem_vertexLabels index b).mp bF, (index b).property⟩
    rw [Q.vertices] at member
    obtain ⟨i, same⟩ := member
    refine ⟨i, ?_⟩
    apply index.injective
    exact (label_vertex i).trans (Subtype.ext same)
  obtain ⟨i, rfl⟩ := corner_of_member a aF
  have neighbors : (F.vertexLabels index).filter (fun b => P.edgeGraph.Adj (index (label i)) (index b)) =
      {label (i + 1), label (i + 3)} := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨bF, edge⟩
      obtain ⟨j, rfl⟩ := corner_of_member b bF
      rw [label_vertex, label_vertex, Q.adjacent_iff_consecutive] at edge
      rcases edge with next | previous
      · exact Or.inl (congrArg label next)
      · have previous : j = i + 3 := (by decide : ∀ i j : Fin 4, i = j + 1 → j = i + 3) i j previous
        exact Or.inr (congrArg label previous)
    · rintro (rfl | rfl)
      · refine ⟨?_, ?_⟩
        · rw [F.mem_vertexLabels, label_vertex]
          exact Q.corner_mem _
        · rw [label_vertex, label_vertex]
          exact Q.consecutive_adjacent i
      · refine ⟨?_, ?_⟩
        · rw [F.mem_vertexLabels, label_vertex]
          exact Q.corner_mem _
        · rw [label_vertex, label_vertex, Q.adjacent_iff_consecutive]
          exact Or.inr ((by decide : ∀ i : Fin 4, i = i + 3 + 1) i)
  rw [neighbors, Finset.card_pair]
  · exact label_injective.ne ((by decide : ∀ i : Fin 4, i + 1 ≠ i + 3) i)

end SixVertexUnfolding.ConvexPolyhedron.Face
