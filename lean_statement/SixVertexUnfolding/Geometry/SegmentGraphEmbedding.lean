import SixVertexUnfolding.Geometry.ConsecutiveSegmentSeparation

/-! The constructed segment graph is embedded: different open edges
cannot meet, and no graph vertex lies in an open edge. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- Intersecting open graph edges have the same endpoints, possibly in reverse order. -/
theorem segmentGraph_open_edges_meet {P : ConvexPolyhedron} (segments : Set P.FaceSegment)
    {a b c d : segmentVertices segments}
    (first_edge : (segmentGraph segments).Adj a b) (second_edge : (segmentGraph segments).Adj c d)
    {x : Space} (first : x ∈ openSegment ℝ (a : Space) (b : Space))
    (second : x ∈ openSegment ℝ (c : Space) (d : Space)) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  obtain ⟨s, hs, aS, bS⟩ := first_edge.2.1
  obtain ⟨t, ht, cT, dT⟩ := second_edge.2.1
  have xS := s.convex.segment_subset aS bS (openSegment_subset_segment ℝ _ _ first)
  have xT := t.convex.segment_subset cT dT (openSegment_subset_segment ℝ _ _ second)
  have same_line : s.supportingLine = t.supportingLine := by
    by_contra different
    have crossing : x ∈ segmentVertices segments := Or.inr ⟨s, hs, t, ht, different, xS, xT⟩
    exact disjoint_left.mp first_edge.2.2 first crossing
  have ab : (a : Space) ≠ (b : Space) := fun equal => first_edge.1 (Subtype.ext equal)
  have cd : (c : Space) ≠ (d : Space) := fun equal => second_edge.1 (Subtype.ext equal)
  have span : affineSpan ℝ ({(a : Space), (b : Space)} : Set Space) = s.supportingLine :=
    affineSpan_pair_eq_of_mem_of_mem_of_ne (s.on_supportingLine aS) (s.on_supportingLine bS) ab
  have c_line : (c : Space) ∈ affineSpan ℝ ({(a : Space), (b : Space)} : Set Space) := by
    rw [span, same_line]
    exact t.on_supportingLine cT
  have d_line : (d : Space) ∈ affineSpan ℝ ({(a : Space), (b : Space)} : Set Space) := by
    rw [span, same_line]
    exact t.on_supportingLine dT
  rcases consecutive_collinear_segments (segmentVertices segments) a.property b.property c.property d.property
    ab cd c_line d_line first_edge.2.2 second_edge.2.2 first second with ⟨ac, bd⟩ | ⟨ad, bc⟩
  · exact Or.inl ⟨Subtype.ext ac, Subtype.ext bd⟩
  · exact Or.inr ⟨Subtype.ext ad, Subtype.ext bc⟩

/-- Distinct unoriented graph edges have disjoint open straight traces. -/
theorem segmentGraph_open_edges_disjoint {P : ConvexPolyhedron} (segments : Set P.FaceSegment)
    {a b c d : segmentVertices segments}
    (first_edge : (segmentGraph segments).Adj a b) (second_edge : (segmentGraph segments).Adj c d)
    (different : ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c))) :
    Disjoint (openSegment ℝ (a : Space) (b : Space)) (openSegment ℝ (c : Space) (d : Space)) := by
  apply disjoint_left.mpr
  intro x hx hy
  exact different (segmentGraph_open_edges_meet segments first_edge second_edge hx hy)

end SixVertexUnfolding.ConvexPolyhedron
