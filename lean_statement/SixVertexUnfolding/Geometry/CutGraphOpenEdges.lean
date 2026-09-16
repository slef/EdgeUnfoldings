import SixVertexUnfolding.Geometry.EmbeddedGraphGluing

/-! A connected piece of the cut trace that avoids every graph vertex
cannot switch from one open graph edge to another.
-/

namespace SixVertexUnfolding.ConvexPolyhedron.EmbeddedCutGraph

open Set

variable {P : ConvexPolyhedron} {a : frontier P.body} (K : P.EmbeddedCutGraph a)

/-- A connected subset of the trace, avoiding graph vertices and meeting
one open edge, stays entirely in that edge. -/
theorem preconnected_in_one_open_edge {S : Set Space} (connected : IsPreconnected S)
    (on_trace : S ⊆ P.cutSetInSpace a) (no_vertices : Disjoint S K.vertices)
    {u v : K.vertices} (edge : K.graph.Adj u v)
    (meets : (S ∩ openSegment ℝ (u : Space) (v : Space)).Nonempty) :
    S ⊆ openSegment ℝ (u : Space) (v : Space) := by
  classical
  letI : Finite K.vertices := K.finite_vertices
  let otherEdges := {pq : K.vertices × K.vertices // K.graph.Adj pq.1 pq.2 ∧
    ¬ ((pq.1 = u ∧ pq.2 = v) ∨ (pq.1 = v ∧ pq.2 = u))}
  let selected := segment ℝ (u : Space) (v : Space)
  let other : Set Space := K.vertices ∪ ⋃ e : otherEdges,
    segment ℝ (e.val.1 : Space) (e.val.2 : Space)
  have closed_segment (p q : Space) : IsClosed (segment ℝ p q) := by
    let line : ℝ →ᵃ[ℝ] Space := AffineMap.lineMap p q
    rw [segment_eq_image_lineMap]
    exact (isCompact_Icc.image line.continuous_of_finiteDimensional).isClosed
  have closed_other : IsClosed other := K.finite_vertices.isClosed.union
    (isClosed_iUnion_of_finite (fun e : otherEdges => closed_segment e.val.1 e.val.2))
  have interior {x : Space} (hx : x ∈ S) {p q : K.vertices}
      (member : x ∈ segment ℝ (p : Space) (q : Space)) :
      x ∈ openSegment ℝ (p : Space) (q : Space) :=
    mem_openSegment_of_ne_left_right
      (fun same => disjoint_left.mp no_vertices hx (same ▸ p.property))
      (fun same => disjoint_left.mp no_vertices hx (same ▸ q.property)) member
  have covered : S ⊆ selected ∪ other := by
    intro x hx
    rcases (K.trace x).mp (on_trace hx) with vertex | ⟨p, q, pq, member⟩
    · exact (disjoint_left.mp no_vertices hx vertex).elim
    · by_cases same : (p = u ∧ q = v) ∨ (p = v ∧ q = u)
      · rcases same with ⟨pu, qv⟩ | ⟨pv, qu⟩
        · apply Or.inl
          change x ∈ segment ℝ (u : Space) (v : Space)
          rw [← pu, ← qv]
          exact openSegment_subset_segment ℝ _ _ member
        · apply Or.inl
          change x ∈ segment ℝ (u : Space) (v : Space)
          rw [← qu, ← pv, segment_symm]
          exact openSegment_subset_segment ℝ _ _ member
      · exact Or.inr (Or.inr (mem_iUnion.mpr ⟨⟨(p, q), pq, same⟩,
          openSegment_subset_segment ℝ _ _ member⟩))
  have separated : S ∩ (selected ∩ other) = ∅ := by
    apply subset_empty_iff.mp
    rintro x ⟨hx, on_selected, in_other⟩
    rcases in_other with vertex | in_other
    · exact disjoint_left.mp no_vertices hx vertex
    · obtain ⟨e, member⟩ := mem_iUnion.mp in_other
      have alternatives := K.open_edges_meet e.val.1 e.val.2 u v e.property.1 edge x
        (interior hx member) (interior hx on_selected)
      exact e.property.2 alternatives
  have alternatives := (isPreconnected_iff_subset_of_disjoint_closed.mp connected)
    selected other (closed_segment u v) closed_other covered separated
  have in_selected : S ⊆ selected := alternatives.resolve_right (by
    intro all_other
    obtain ⟨x, hx, member⟩ := meets
    have forbidden : x ∈ S ∩ (selected ∩ other) :=
      ⟨hx, openSegment_subset_segment ℝ _ _ member, all_other hx⟩
    rw [separated] at forbidden
    exact forbidden)
  exact fun x hx => interior hx (in_selected hx)

end SixVertexUnfolding.ConvexPolyhedron.EmbeddedCutGraph
