import SixVertexUnfolding.Geometry.EmbeddedGraphGluing

/-! Near an embedded graph vertex, only its incident edges occur. At a
leaf this gives an actual one-sided segment neighborhood in the cut set. -/

namespace SixVertexUnfolding.ConvexPolyhedron.EmbeddedCutGraph

open Set

variable {P : ConvexPolyhedron} {a : frontier P.body} (K : P.EmbeddedCutGraph a)

/-- A sufficiently small neighborhood sees exactly the incident part of the graph. -/
theorem vertex_star_neighborhood (u : K.vertices) :
    ∃ U : Set Space, IsOpen U ∧ (u : Space) ∈ U ∧ ∀ x ∈ U,
      x ∈ P.cutSetInSpace a → x = (u : Space) ∨
        ∃ v : K.vertices, K.graph.Adj u v ∧ x ∈ segment ℝ (u : Space) (v : Space) := by
  letI : Finite K.vertices := K.finite_vertices
  let away : Set Space := (K.vertices \ {(u : Space)}) ∪
    ⋃ p : K.vertices, ⋃ q : K.vertices,
      ⋃ (_ : K.graph.Adj p q ∧ p ≠ u ∧ q ≠ u), segment ℝ (p : Space) (q : Space)
  have closed : IsClosed away := by
    apply (K.finite_vertices.subset diff_subset).isClosed.union
    apply isClosed_iUnion_of_finite
    intro p
    apply isClosed_iUnion_of_finite
    intro q
    apply isClosed_iUnion_of_finite
    intro _
    let line : ℝ →ᵃ[ℝ] Space := AffineMap.lineMap (p : Space) (q : Space)
    rw [segment_eq_image_lineMap]
    exact (isCompact_Icc.image line.continuous_of_finiteDimensional).isClosed
  have absent : (u : Space) ∉ away := by
    rintro (vertex | edge)
    · exact vertex.2 rfl
    · simp only [mem_iUnion] at edge
      obtain ⟨p, q, conditions, member⟩ := edge
      rcases K.vertex_on_edge conditions.1 member with same | same
      · exact conditions.2.1 same.symm
      · exact conditions.2.2 same.symm
  refine ⟨awayᶜ, closed.isOpen_compl, absent, ?_⟩
  intro x near cut
  rcases (K.trace x).mp cut with vertex | ⟨p, q, edge, inside⟩
  · left
    by_contra different
    exact near (Or.inl ⟨vertex, different⟩)
  · by_cases first : p = u
    · subst p
      exact Or.inr ⟨q, edge, openSegment_subset_segment ℝ _ _ inside⟩
    · by_cases second : q = u
      · subst q
        exact Or.inr ⟨p, edge.symm, by rw [segment_symm]; exact openSegment_subset_segment ℝ _ _ inside⟩
      · exfalso
        apply near
        apply Or.inr
        simp only [mem_iUnion]
        exact ⟨p, q, ⟨edge, first, second⟩, openSegment_subset_segment ℝ _ _ inside⟩

/-- If a vertex has just one neighbor, its nearby trace is contained in that one closed edge. -/
theorem leaf_segment_neighborhood (u v : K.vertices)
    (only_neighbor : ∀ w, K.graph.Adj u w → w = v) :
    ∃ U : Set Space, IsOpen U ∧ (u : Space) ∈ U ∧
      U ∩ P.cutSetInSpace a ⊆ segment ℝ (u : Space) (v : Space) := by
  obtain ⟨U, openU, uU, star⟩ := K.vertex_star_neighborhood u
  refine ⟨U, openU, uU, ?_⟩
  intro x hx
  rcases star x hx.1 hx.2 with rfl | ⟨w, edge, member⟩
  · exact left_mem_segment ℝ _ _
  · rwa [only_neighbor w edge] at member

end SixVertexUnfolding.ConvexPolyhedron.EmbeddedCutGraph
