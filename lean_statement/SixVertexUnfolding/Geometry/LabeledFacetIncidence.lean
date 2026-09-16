import SixVertexUnfolding.Geometry.FacetLabels

/-! Original edge incidence transferred to finite sets of original vertex labels. -/

namespace SixVertexUnfolding.ConvexPolyhedron

variable {P : ConvexPolyhedron} (index : Fin 6 ≃ P.Vertex)

/-- All original facets, recorded by their sets of original vertex labels. -/
noncomputable def labeledFacets : Finset (Finset (Fin 6)) :=
  (Set.range (fun F : P.Face => F.vertexLabels index)).toFinite.toFinset

@[simp] theorem mem_labeledFacets (vertices : Finset (Fin 6)) :
    vertices ∈ labeledFacets index ↔ ∃ F : P.Face, F.vertexLabels index = vertices := by
  simp [labeledFacets]

/-- An original edge occurs in exactly two of the labeled original facets. -/
theorem labeledFacets_edge_count (i j : Fin 6) (edge : P.edgeGraph.Adj (index i) (index j)) :
    ((labeledFacets index).filter (fun face => i ∈ face ∧ j ∈ face)).card = 2 := by
  classical
  obtain ⟨F, G, different, iF, jF, iG, jG, only_two⟩ := P.edge_incident_faces (index i) (index j) edge
  have pair : (labeledFacets index).filter (fun face => i ∈ face ∧ j ∈ face) =
      {F.vertexLabels index, G.vertexLabels index} := by
    ext vertices
    simp only [Finset.mem_filter, mem_labeledFacets, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨H, rfl⟩, hi, hj⟩
      rcases only_two H ((H.mem_vertexLabels index i).mp hi) ((H.mem_vertexLabels index j).mp hj) with rfl | rfl
      exacts [Or.inl rfl, Or.inr rfl]
    · rintro (rfl | rfl)
      · exact ⟨⟨F, rfl⟩, (F.mem_vertexLabels index i).mpr iF, (F.mem_vertexLabels index j).mpr jF⟩
      · exact ⟨⟨G, rfl⟩, (G.mem_vertexLabels index i).mpr iG, (G.mem_vertexLabels index j).mpr jG⟩
  rw [pair, Finset.card_pair]
  exact (Face.vertexLabels_injective index).ne different

/-- A distinct nonedge pair occurs together in at most one labeled original facet. -/
theorem labeledFacets_nonedge_count (i j : Fin 6) (different : i ≠ j)
    (nonedge : ¬ P.edgeGraph.Adj (index i) (index j)) :
    ((labeledFacets index).filter (fun face => i ∈ face ∧ j ∈ face)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro left left_mem right right_mem
  obtain ⟨left_mem, il, jl⟩ := Finset.mem_filter.mp left_mem
  obtain ⟨right_mem, ir, jr⟩ := Finset.mem_filter.mp right_mem
  obtain ⟨F, rfl⟩ := (mem_labeledFacets index left).mp left_mem
  obtain ⟨G, rfl⟩ := (mem_labeledFacets index right).mp right_mem
  rw [Face.eq_of_common_nonedge_labels index F G i j different nonedge il jl ir jr]

end SixVertexUnfolding.ConvexPolyhedron
