import SixVertexUnfolding.Geometry.BipyramidVertices

/-! The pole segment crosses the equator triangle, strictly away from its three edges. -/

namespace SixVertexUnfolding.ConvexPolyhedron.BipyramidVertices

variable {P : ConvexPolyhedron} (B : BipyramidVertices P)

/-- The three equator points, with no choice of cyclic order. -/
def equatorPoints : Set Space := Set.range (fun i : Fin 3 => (B.equatorVertex i : Space))

theorem vertices_except_poles :
    (P.vertices : Set Space) \ {(B.top : Space), (B.bottom : Space)} = B.equatorPoints := by
  ext x
  constructor
  · rintro ⟨vertex, other⟩
    rcases B.vertex_cases ⟨x, vertex⟩ with top | bottom | ⟨i, equal⟩
    · exact False.elim (other (Or.inl (congrArg Subtype.val top)))
    · exact False.elim (other (Or.inr (congrArg Subtype.val bottom)))
    · exact ⟨i, (congrArg Subtype.val equal).symm⟩
  · rintro ⟨i, rfl⟩
    refine ⟨(B.equatorVertex i).property, ?_⟩
    rintro (top | bottom)
    · exact B.equator_ne_top i (Subtype.ext top)
    · exact B.equator_ne_bottom i (Subtype.ext bottom)

/-- Neither pole belongs to the equator triangle. -/
theorem pole_not_mem_equator_hull (upper : Bool) :
    (B.poleVertex upper : Space) ∉ convexHull ℝ B.equatorPoints := by
  intro member
  apply P.vertex_not_mem_hull_others (B.poleVertex upper)
  apply convexHull_mono (show B.equatorPoints ⊆
    (P.vertices : Set Space) \ {(B.poleVertex upper : Space)} from ?_) member
  rintro x ⟨i, rfl⟩
  exact ⟨(B.equatorVertex i).property,
    fun equal => B.pole_ne_equator upper i (Subtype.ext equal.symm)⟩

/-- Radon's intersecting pair must be the unique nonedge: the two poles. -/
theorem pole_segment_meets_equator (size : P.vertices.card = 5) :
    (segment ℝ (B.top : Space) (B.bottom : Space) ∩ convexHull ℝ B.equatorPoints).Nonempty := by
  let index : Fin 5 ≃ P.Vertex := (Fintype.equivFinOfCardEq (P.vertex_card.trans size)).symm
  obtain ⟨i, j, different, x, on_segment, in_hull⟩ :=
    P.five_distinct_vertices_have_radon_pair index index.injective
  have pair : s(index i, index j) = s(B.top, B.bottom) := by
    by_contra other
    have edge := (B.edges (index i) (index j)).mpr
      ⟨fun same => different (index.injective same), other⟩
    exact Set.disjoint_left.mp (P.edge_disjoint_hull_others (index i) (index j) edge) on_segment in_hull
  rcases Sym2.eq_iff.mp pair with ⟨itop, jbottom⟩ | ⟨ibottom, jtop⟩
  · rw [itop, jbottom] at on_segment in_hull
    rw [B.vertices_except_poles] at in_hull
    exact ⟨x, on_segment, in_hull⟩
  · rw [ibottom, jtop] at on_segment in_hull
    rw [segment_symm] at on_segment
    rw [Set.pair_comm, B.vertices_except_poles] at in_hull
    exact ⟨x, on_segment, in_hull⟩

/-- The crossing lies strictly inside the pole segment and on no equator edge. -/
theorem strict_equator_crossing (size : P.vertices.card = 5) :
    ∃ x : Space, x ∈ openSegment ℝ (B.top : Space) (B.bottom : Space) ∧
      x ∈ convexHull ℝ B.equatorPoints ∧
      ∀ i j : Fin 3, i ≠ j → x ∉ segment ℝ (B.equatorVertex i : Space) (B.equatorVertex j : Space) := by
  obtain ⟨x, on_segment, in_triangle⟩ := B.pole_segment_meets_equator size
  have top_ne : (B.top : Space) ≠ x := fun equal =>
    B.pole_not_mem_equator_hull true (equal ▸ in_triangle)
  have bottom_ne : (B.bottom : Space) ≠ x := fun equal =>
    B.pole_not_mem_equator_hull false (equal ▸ in_triangle)
  refine ⟨x, mem_openSegment_of_ne_left_right top_ne bottom_ne on_segment, in_triangle, ?_⟩
  intro i j different on_edge
  have in_others : x ∈ convexHull ℝ ((P.vertices : Set Space) \
      {(B.equatorVertex i : Space), (B.equatorVertex j : Space)}) := by
    rw [← convexHull_pair] at on_segment
    apply convexHull_mono (show {(B.top : Space), (B.bottom : Space)} ⊆
      (P.vertices : Set Space) \ {(B.equatorVertex i : Space), (B.equatorVertex j : Space)} from ?_) on_segment
    intro y member
    rcases member with top | bottom
    · subst y
      refine ⟨B.top.property, ?_⟩
      rintro (same | same)
      · exact B.equator_ne_top i (Subtype.ext same.symm)
      · exact B.equator_ne_top j (Subtype.ext same.symm)
    · subst y
      refine ⟨B.bottom.property, ?_⟩
      rintro (same | same)
      · exact B.equator_ne_bottom i (Subtype.ext same.symm)
      · exact B.equator_ne_bottom j (Subtype.ext same.symm)
  exact Set.disjoint_left.mp
    (P.edge_disjoint_hull_others (B.equatorVertex i) (B.equatorVertex j)
      (B.equator_adjacent i j different)) on_edge in_others

end SixVertexUnfolding.ConvexPolyhedron.BipyramidVertices
