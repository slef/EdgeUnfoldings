import SixVertexUnfolding.Geometry.ThreeByThree

/-! Exclude the unwanted two-triple graph patterns by counting original facet edges. -/

namespace SixVertexUnfolding.ConvexPolyhedron.ThreeByThree

variable {P : ConvexPolyhedron} (B : P.ThreeByThree)

/-- A triangular facet has one same-triple edge when no original vertex is universal. -/
theorem triangle_internal_count
    (no_universal : ¬ ∃ v : P.Vertex, ∀ w, w ≠ v → P.edgeGraph.Adj v w)
    (F : P.Face) (triangle : (F.val ∩ (P.vertices : Set Space)).ncard = 3) :
    ∑ e ∈ F.edgeFinset, internalEdgeWeight B.color e = 1 := by
  obtain ⟨a, b, c, ab, ac, bc, vertices⟩ := Set.ncard_eq_three.mp triangle
  have vertex (x : Space) (member : x ∈ ({a, b, c} : Set Space)) : x ∈ P.vertices :=
    (vertices ▸ member).2
  let A : P.Vertex := ⟨a, vertex a (Or.inl rfl)⟩
  let C : P.Vertex := ⟨c, vertex c (Or.inr (Or.inr rfl))⟩
  let D : P.Vertex := ⟨b, vertex b (Or.inr (Or.inl rfl))⟩
  have AD : A ≠ D := fun same => ab (congrArg Subtype.val same)
  have AC : A ≠ C := fun same => ac (congrArg Subtype.val same)
  have DC : D ≠ C := fun same => bc (congrArg Subtype.val same)
  have edge_AD := F.triangle_vertices_adjacent A D C AD AC DC vertices
  have edge_AC := F.triangle_vertices_adjacent A C D AC AD DC.symm (by
    rw [vertices]; ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto)
  exact F.triangle_internal_edge_sum B.color A D C AD AC DC vertices
    (B.no_monochromatic_triangle no_universal A D C AD AC DC edge_AD edge_AC)

/-- An original quadrilateral has no same-triple boundary edge. -/
theorem quadrilateral_internal_count (F : P.Face)
    (four : (F.val ∩ (P.vertices : Set Space)).ncard = 4) :
    ∑ e ∈ F.edgeFinset, internalEdgeWeight B.color e = 0 := by
  obtain ⟨Q⟩ := F.exists_quadrilateral four
  exact Q.internal_edge_sum_zero B.adjacent_of_different_color
    (B.no_four_same_color Q.corner Q.distinct)

include B in
/-- In the remaining six-vertex family, two triples cannot have all nine cross-edges. -/
theorem impossible
    (no_universal : ¬ ∃ v : P.Vertex, ∀ w, w ≠ v → P.edgeGraph.Adj v w)
    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4) : False := by
  classical
  letI : Fintype P.Face := Fintype.ofFinite _
  let internal := ∑ e ∈ P.originalEdges, internalEdgeWeight B.color e
  let quadrilaterals := ∑ F : P.Face, if (F.val ∩ (P.vertices : Set Space)).ncard = 4 then 1 else 0
  have per_face (F : P.Face) :
      F.edgeFinset.card = 3 * (∑ e ∈ F.edgeFinset, internalEdgeWeight B.color e) +
        4 * (if (F.val ∩ (P.vertices : Set Space)).ncard = 4 then 1 else 0) := by
    rcases small_faces F with triangle | quadrilateral
    · rw [F.triangle_edge_count triangle, B.triangle_internal_count no_universal F triangle]
      simp [triangle]
    · rw [F.quadrilateral_edge_count quadrilateral, B.quadrilateral_internal_count F quadrilateral]
      simp [quadrilateral]
  have face_count : (∑ F : P.Face, F.edgeFinset.card) = 6 * internal + 4 * quadrilaterals := by
    simp_rw [per_face]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      P.weighted_facet_edge_count (internalEdgeWeight B.color)]
    change 3 * (2 * internal) + 4 * quadrilaterals = _
    ring
  have twice_edges := P.weighted_facet_edge_count (fun _ => 1)
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at twice_edges
  have total := B.total_edge_count
  change internal + 9 = P.originalEdges.card at total
  omega

end SixVertexUnfolding.ConvexPolyhedron.ThreeByThree
