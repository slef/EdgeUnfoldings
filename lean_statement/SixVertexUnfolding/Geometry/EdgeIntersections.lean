import SixVertexUnfolding.Geometry.EdgeGraph

/-! Straight original edges cannot cross or overlap except at common endpoints. -/

namespace SixVertexUnfolding.ConvexPolyhedron

/-- Each edge segment is an exposed subset of the convex solid. -/
theorem edgeGraph_segment_isExposed (P : ConvexPolyhedron) {a b : P.Vertex}
    (adjacent : P.edgeGraph.Adj a b) : IsExposed ℝ P.body (segment ℝ (a : Space) (b : Space)) := by
  obtain ⟨_, F, G, _, edge_eq⟩ := adjacent
  rw [← edge_eq]
  exact F.intersection_isExposed G

/-- If an edge meets the interior of another edge, their unordered endpoint pairs coincide. -/
theorem edges_eq_of_meeting_open_segment (P : ConvexPolyhedron) {a b c d : P.Vertex}
    (ab : P.edgeGraph.Adj a b) (cd : P.edgeGraph.Adj c d) {x : Space}
    (inside : x ∈ openSegment ℝ (a : Space) (b : Space))
    (on_edge : x ∈ segment ℝ (c : Space) (d : Space)) : s(a, b) = s(c, d) := by
  have exposed := (P.edgeGraph_segment_isExposed cd).isExtreme
  have a_on := exposed.left_mem_of_mem_openSegment (P.vertices_subset_body a.property)
    (P.vertices_subset_body b.property) on_edge inside
  have b_on := exposed.right_mem_of_mem_openSegment (P.vertices_subset_body a.property)
    (P.vertices_subset_body b.property) on_edge inside
  have a_endpoint := P.vertex_in_segment_is_endpoint a.property
    (P.vertices_subset_body c.property) (P.vertices_subset_body d.property) a_on
  have b_endpoint := P.vertex_in_segment_is_endpoint b.property
    (P.vertices_subset_body c.property) (P.vertices_subset_body d.property) b_on
  have endpoints_a : a = c ∨ a = d := a_endpoint.imp
    (fun equal => Subtype.ext equal.symm) (fun equal => Subtype.ext equal.symm)
  have endpoints_b : b = c ∨ b = d := b_endpoint.imp
    (fun equal => Subtype.ext equal.symm) (fun equal => Subtype.ext equal.symm)
  rw [Sym2.eq_iff]
  rcases endpoints_a with ac | ad <;> rcases endpoints_b with bc | bd
  · exact False.elim (ab.ne (ac.trans bc.symm))
  · exact Or.inl ⟨ac, bd⟩
  · exact Or.inr ⟨ad, bc⟩
  · exact False.elim (ab.ne (ad.trans bd.symm))

/-- Different original edges meet only at a point that is an endpoint of both edges. -/
theorem edge_intersection_is_common_endpoint (P : ConvexPolyhedron) {a b c d : P.Vertex}
    (ab : P.edgeGraph.Adj a b) (cd : P.edgeGraph.Adj c d) (different : s(a, b) ≠ s(c, d))
    {x : Space} (on_ab : x ∈ segment ℝ (a : Space) (b : Space))
    (on_cd : x ∈ segment ℝ (c : Space) (d : Space)) :
    (x = (a : Space) ∨ x = (b : Space)) ∧ (x = (c : Space) ∨ x = (d : Space)) := by
  have left_endpoint : x = (a : Space) ∨ x = (b : Space) := by
    by_contra neither
    push Not at neither
    have inside := mem_openSegment_of_ne_left_right neither.1.symm neither.2.symm on_ab
    exact different (P.edges_eq_of_meeting_open_segment ab cd inside on_cd)
  have vertex : x ∈ P.vertices := by
    rcases left_endpoint with rfl | rfl
    exacts [a.property, b.property]
  have right_endpoint := P.vertex_in_segment_is_endpoint vertex
    (P.vertices_subset_body c.property) (P.vertices_subset_body d.property) on_cd
  exact ⟨left_endpoint, right_endpoint.imp Eq.symm Eq.symm⟩

/-- Distinct original edge interiors are disjoint in three-space. -/
theorem open_edges_disjoint (P : ConvexPolyhedron) {a b c d : P.Vertex}
    (ab : P.edgeGraph.Adj a b) (cd : P.edgeGraph.Adj c d) (different : s(a, b) ≠ s(c, d)) :
    Disjoint (openSegment ℝ (a : Space) (b : Space))
      (openSegment ℝ (c : Space) (d : Space)) := by
  apply Set.disjoint_left.mpr
  intro x on_ab on_cd
  exact different (P.edges_eq_of_meeting_open_segment ab cd on_ab
    (openSegment_subset_segment ℝ _ _ on_cd))

end SixVertexUnfolding.ConvexPolyhedron
