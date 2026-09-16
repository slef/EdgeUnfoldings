import SixVertexUnfolding.Geometry.QuadrilateralVertices

/-! A quadrilateral has exactly four original boundary edges and two nonedge diagonals. -/

namespace SixVertexUnfolding

/-- Crossing diagonals put the two remaining corners strictly below a side's exposing height. -/
theorem quadrilateral_edge_height (a b c d : Space)
    (noncollinear : ¬ Collinear ℝ ({a, b, c} : Set Space))
    (crossing : ∃ x, x ∈ openSegment ℝ a c ∧ x ∈ openSegment ℝ b d) :
    ∃ q : Space, inner ℝ q a = inner ℝ q b ∧
      inner ℝ q c < inner ℝ q a ∧ inner ℝ q d < inner ℝ q a := by
  obtain ⟨q, tied, lower⟩ := triangle_edge_height a b c noncollinear
  obtain ⟨x, ⟨s, t, _, tpos, st, left⟩, ⟨u, v, _, vpos, uv, right⟩⟩ := crossing
  have balance := congrArg (inner ℝ q) (left.trans right.symm)
  simp only [inner_add_right, inner_smul_right, ← tied] at balance
  have weighted : t * (inner ℝ q c - inner ℝ q a) = v * (inner ℝ q d - inner ℝ q a) := by
    nlinarith [congrArg (fun z : ℝ => z * inner ℝ q a) st,
      congrArg (fun z : ℝ => z * inner ℝ q a) uv]
  have right_negative : v * (inner ℝ q d - inner ℝ q a) < 0 := by
    rw [← weighted]
    exact mul_neg_of_pos_of_neg tpos (sub_neg.mpr lower)
  exact ⟨q, tied, lower, by nlinarith⟩

namespace ConvexPolyhedron.Face.Quadrilateral

variable {P : ConvexPolyhedron} {F : P.Face} (Q : F.Quadrilateral)

theorem corner_mem (i : Fin 4) : (Q.corner i : Space) ∈ F.val := by
  have member : (Q.corner i : Space) ∈ F.val ∩ (P.vertices : Set Space) := by
    rw [Q.vertices]
    exact ⟨i, rfl⟩
  exact member.1

theorem corner_ne (i j : Fin 4) (different : i ≠ j) : Q.corner i ≠ Q.corner j :=
  fun same => different (Q.distinct same)

/-- The same crossing description holds after starting at any of the four corners. -/
theorem cyclic_crossing (i : Fin 4) :
    ∃ x : Space, x ∈ openSegment ℝ (Q.corner i : Space) (Q.corner (i + 2) : Space) ∧
      x ∈ openSegment ℝ (Q.corner (i + 1) : Space) (Q.corner (i + 3) : Space) := by
  obtain ⟨x, first, second⟩ := Q.crossing
  have first_reverse : x ∈ openSegment ℝ (Q.corner 2 : Space) (Q.corner 0 : Space) := by
    rwa [openSegment_symm]
  have second_reverse : x ∈ openSegment ℝ (Q.corner 3 : Space) (Q.corner 1 : Space) := by
    rwa [openSegment_symm]
  fin_cases i
  · exact ⟨x, first, second⟩
  · exact ⟨x, second, first_reverse⟩
  · exact ⟨x, first_reverse, second_reverse⟩
  · exact ⟨x, second_reverse, first⟩

/-- Every consecutive pair is an original edge of the solid. -/
theorem consecutive_adjacent (i : Fin 4) : P.edgeGraph.Adj (Q.corner i) (Q.corner (i + 1)) := by
  have i1 : i ≠ i + 1 := by fin_cases i <;> decide
  have i2 : i ≠ i + 2 := by fin_cases i <;> decide
  have next2 : i + 1 ≠ i + 2 := by fin_cases i <;> decide
  obtain ⟨q, tied, lower2, lower3⟩ := quadrilateral_edge_height
    (Q.corner i) (Q.corner (i + 1)) (Q.corner (i + 2)) (Q.corner (i + 3))
    (P.no_three_collinear_vertices (Q.corner i).property (Q.corner (i + 1)).property
      (Q.corner (i + 2)).property (fun same => Q.corner_ne i (i + 1) i1 (Subtype.ext same))
      (fun same => Q.corner_ne i (i + 2) i2 (Subtype.ext same))
      (fun same => Q.corner_ne (i + 1) (i + 2) next2 (Subtype.ext same)))
    (Q.cyclic_crossing i)
  apply F.edge_of_exposing_height (Q.corner i) (Q.corner (i + 1)) (Q.corner_ne i (i + 1) i1)
    (Q.corner_mem i) (Q.corner_mem (i + 1)) q tied
  intro w on_face wi wnext
  obtain ⟨j, same⟩ := Q.vertices ▸ (show (w : Space) ∈ F.val ∩ (P.vertices : Set Space) from
    ⟨on_face, w.property⟩)
  have vertex_eq : Q.corner j = w := Subtype.ext same
  have remaining : j = i + 2 ∨ j = i + 3 := by
    have ji : j ≠ i := fun eq => wi (vertex_eq.symm.trans (congrArg Q.corner eq))
    have jnext : j ≠ i + 1 := fun eq => wnext (vertex_eq.symm.trans (congrArg Q.corner eq))
    fin_cases i <;> fin_cases j <;> simp_all
  rcases remaining with rfl | rfl
  · simpa only [← vertex_eq] using lower2
  · simpa only [← vertex_eq] using lower3

/-- A diagonal crosses the segment joining the other two original vertices, so is not an edge. -/
theorem diagonal_not_adjacent (i : Fin 4) :
    ¬ P.edgeGraph.Adj (Q.corner i) (Q.corner (i + 2)) := by
  intro edge
  obtain ⟨x, first, second⟩ := Q.cyclic_crossing i
  have in_others : x ∈ convexHull ℝ ((P.vertices : Set Space) \
      {(Q.corner i : Space), (Q.corner (i + 2) : Space)}) := by
    apply convexHull_mono (show {(Q.corner (i + 1) : Space), (Q.corner (i + 3) : Space)} ⊆
      (P.vertices : Set Space) \ {(Q.corner i : Space), (Q.corner (i + 2) : Space)} from ?_)
      (by rw [convexHull_pair]; exact openSegment_subset_segment ℝ _ _ second)
    rintro y (rfl | rfl)
    · refine ⟨(Q.corner (i + 1)).property, ?_⟩
      rintro (same | same)
      · have impossible := Q.distinct (Subtype.ext same)
        fin_cases i <;> simp_all
      · have impossible := Q.distinct (Subtype.ext same)
        fin_cases i <;> simp_all
    · refine ⟨(Q.corner (i + 3)).property, ?_⟩
      rintro (same | same)
      · have impossible := Q.distinct (Subtype.ext same)
        fin_cases i <;> simp_all
      · have impossible := Q.distinct (Subtype.ext same)
        fin_cases i <;> simp_all
  exact Set.disjoint_left.mp (P.edge_disjoint_hull_others (Q.corner i) (Q.corner (i + 2)) edge)
    (openSegment_subset_segment ℝ _ _ first) in_others

/-- The original edge graph on a quadrilateral's vertices is exactly the four-cycle. -/
theorem adjacent_iff_consecutive (i j : Fin 4) :
    P.edgeGraph.Adj (Q.corner i) (Q.corner j) ↔ j = i + 1 ∨ i = j + 1 := by
  constructor
  · intro edge
    have distinct := fun same : i = j => edge.ne (congrArg Q.corner same)
    have not_diagonal : j ≠ i + 2 := fun same => Q.diagonal_not_adjacent i (same ▸ edge)
    fin_cases i <;> fin_cases j <;> simp_all
  · rintro (rfl | rfl)
    · exact Q.consecutive_adjacent i
    · exact (Q.consecutive_adjacent j).symm

end ConvexPolyhedron.Face.Quadrilateral
end SixVertexUnfolding
