import SixVertexUnfolding.Geometry.EmbeddedGraphGluing

/-! The interior of an embedded graph edge is open in the graph trace.
Remove all vertices and all other closed edges to obtain its neighborhood. -/

namespace SixVertexUnfolding.ConvexPolyhedron.EmbeddedCutGraph

open Set

variable {P : ConvexPolyhedron} {a : frontier P.body} (K : P.EmbeddedCutGraph a)

/-- An open graph edge is the intersection of the trace with an ambient open set. -/
theorem open_edge_neighborhood {u v : K.vertices} (edge : K.graph.Adj u v) :
    ∃ U : Set Space, IsOpen U ∧ U ∩ P.cutSetInSpace a = openSegment ℝ (u : Space) (v : Space) := by
  letI : Finite K.vertices := K.finite_vertices
  let away : Set Space := K.vertices ∪ ⋃ w : K.vertices, ⋃ z : K.vertices,
    ⋃ (_ : K.graph.Adj w z ∧ ¬ ((u = w ∧ v = z) ∨ (u = z ∧ v = w))), segment ℝ (w : Space) (z : Space)
  have closed : IsClosed away := by
    apply K.finite_vertices.isClosed.union
    apply isClosed_iUnion_of_finite
    intro w
    apply isClosed_iUnion_of_finite
    intro z
    apply isClosed_iUnion_of_finite
    intro _
    let line : ℝ →ᵃ[ℝ] Space := AffineMap.lineMap (w : Space) (z : Space)
    rw [segment_eq_image_lineMap]
    exact (isCompact_Icc.image line.continuous_of_finiteDimensional).isClosed
  refine ⟨awayᶜ, closed.isOpen_compl, ?_⟩
  ext x
  constructor
  · rintro ⟨outside, cut⟩
    rcases (K.trace x).mp cut with vertex | ⟨w, z, other, inside⟩
    · exact (outside (Or.inl vertex)).elim
    · by_cases same : (u = w ∧ v = z) ∨ (u = z ∧ v = w)
      · rcases same with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact inside
        · rwa [openSegment_symm]
      · exfalso
        apply outside
        exact Or.inr (mem_iUnion.mpr ⟨w, mem_iUnion.mpr ⟨z, mem_iUnion.mpr
          ⟨⟨other, same⟩, openSegment_subset_segment ℝ _ _ inside⟩⟩⟩)
  · intro inside
    have nonvertex : x ∉ K.vertices := fun hx => disjoint_left.mp (K.no_vertex_inside u v edge) inside hx
    refine ⟨?_, (K.trace x).mpr (Or.inr ⟨u, v, edge, inside⟩)⟩
    rintro (vertex | other)
    · exact nonvertex vertex
    · obtain ⟨w, other⟩ := mem_iUnion.mp other
      obtain ⟨z, other⟩ := mem_iUnion.mp other
      obtain ⟨conditions, member⟩ := mem_iUnion.mp other
      have open_member : x ∈ openSegment ℝ (w : Space) (z : Space) := mem_openSegment_of_ne_left_right
        (fun same => nonvertex (same ▸ w.property)) (fun same => nonvertex (same ▸ z.property)) member
      exact conditions.2 (K.open_edges_meet u v w z edge conditions.1 x inside open_member)

/-- The same openness in the boundary-valued cut set used by the endpoint map. -/
theorem open_edge_isOpen {u v : K.vertices} (edge : K.graph.Adj u v) :
    IsOpen {c : P.cutSet a | (c.val : Space) ∈ openSegment ℝ (u : Space) (v : Space)} := by
  obtain ⟨U, openU, trace⟩ := K.open_edge_neighborhood edge
  have equal : {c : P.cutSet a | (c.val : Space) ∈ openSegment ℝ (u : Space) (v : Space)} =
      (fun c : P.cutSet a => (c.val : Space)) ⁻¹' U := by
    ext c
    have cut : (c.val : Space) ∈ P.cutSetInSpace a := (P.mem_cutSetInSpace a c.val).mpr c.property
    simp only [← trace, mem_setOf_eq, mem_inter_iff, mem_preimage, cut, and_true]
  rw [equal]
  exact openU.preimage (continuous_subtype_val.comp continuous_subtype_val)

end SixVertexUnfolding.ConvexPolyhedron.EmbeddedCutGraph
