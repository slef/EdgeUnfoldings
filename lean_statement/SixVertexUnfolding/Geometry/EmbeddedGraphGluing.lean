import SixVertexUnfolding.Geometry.EmbeddedGraphComponents

/-! Continuous functions on the finitely many closed graph edges glue to
continuous functions on the actual cut trace. Isolated graph vertices are included. -/

namespace SixVertexUnfolding.ConvexPolyhedron.EmbeddedCutGraph

open Set

variable {P : ConvexPolyhedron} {a : frontier P.body} (K : P.EmbeddedCutGraph a)

theorem vertex_in_trace (u : K.vertices) : (u : Space) ∈ P.cutSetInSpace a :=
  (K.trace u).mpr (Or.inl u.property)

theorem closed_edge_in_trace {u v : K.vertices} (edge : K.graph.Adj u v) :
    segment ℝ (u : Space) (v : Space) ⊆ P.cutSetInSpace a := by
  apply (openSegment_subset_iff_segment_subset (K.vertex_in_trace u) (K.vertex_in_trace v)).mp
  intro x hx
  exact (K.trace x).mpr (Or.inr ⟨u, v, edge, hx⟩)

/-- The closed graph edges, together with the finite vertex set, cover exactly the cut set. -/
theorem closed_edges_cover :
    K.vertices ∪ ⋃ e : {p : K.vertices × K.vertices // K.graph.Adj p.1 p.2},
      segment ℝ (e.val.1 : Space) (e.val.2 : Space) = P.cutSetInSpace a := by
  ext x
  constructor
  · rintro (vertex | on_edge)
    · exact (K.trace x).mpr (Or.inl vertex)
    · obtain ⟨e, hx⟩ := mem_iUnion.mp on_edge
      exact K.closed_edge_in_trace e.property hx
  · intro member
    rcases (K.trace x).mp member with vertex | ⟨u, v, edge, hx⟩
    · exact Or.inl vertex
    · exact Or.inr (mem_iUnion.mpr ⟨⟨(u, v), edge⟩, openSegment_subset_segment ℝ _ _ hx⟩)

/-- Checking continuity on the closed edges suffices, because this graph is finite. -/
theorem continuous_on_trace_of_edges {Y : Type*} [TopologicalSpace Y] (f : Space → Y)
    (on_edges : ∀ u v : K.vertices, K.graph.Adj u v →
      ContinuousOn f (segment ℝ (u : Space) (v : Space))) : ContinuousOn f (P.cutSetInSpace a) := by
  letI : Finite K.vertices := K.finite_vertices
  let E := {p : K.vertices × K.vertices // K.graph.Adj p.1 p.2}
  let pieces : E → Set Space := fun e => segment ℝ (e.val.1 : Space) (e.val.2 : Space)
  have closed (e : E) : IsClosed (pieces e) := by
    let line : ℝ →ᵃ[ℝ] Space := AffineMap.lineMap (e.val.1 : Space) (e.val.2 : Space)
    change IsClosed (segment ℝ (e.val.1 : Space) (e.val.2 : Space))
    rw [segment_eq_image_lineMap]
    exact (isCompact_Icc.image line.continuous_of_finiteDimensional).isClosed
  have continuous_edges : ContinuousOn f (⋃ e, pieces e) :=
    (locallyFinite_of_finite pieces).continuousOn_iUnion closed
      (fun e => on_edges e.val.1 e.val.2 e.property)
  rw [← K.closed_edges_cover]
  exact (K.finite_vertices.continuousOn f).union_of_isClosed continuous_edges
    K.finite_vertices.isClosed (isClosed_iUnion_of_finite closed)

/-- Traverse a graph edge as a continuous path in the actual cut trace. -/
noncomputable def edgePath {u v : K.vertices} (edge : K.graph.Adj u v) : C(unitInterval, P.cutSetInSpace a) := by
  let line : ℝ →ᵃ[ℝ] Space := AffineMap.lineMap (u : Space) (v : Space)
  refine ⟨fun t => ⟨line t, K.closed_edge_in_trace edge ?_⟩,
    (line.continuous_of_finiteDimensional.comp continuous_subtype_val).subtype_mk _⟩
  rw [segment_eq_image_lineMap]
  exact ⟨t, t.property, rfl⟩

theorem edgePath_zero {u v : K.vertices} (edge : K.graph.Adj u v) :
    K.edgePath edge 0 = ⟨u, K.vertex_in_trace u⟩ := by
  apply Subtype.ext
  exact AffineMap.lineMap_apply_zero _ _

theorem edgePath_one {u v : K.vertices} (edge : K.graph.Adj u v) :
    K.edgePath edge 1 = ⟨v, K.vertex_in_trace v⟩ := by
  apply Subtype.ext
  exact AffineMap.lineMap_apply_one _ _

end SixVertexUnfolding.ConvexPolyhedron.EmbeddedCutGraph
