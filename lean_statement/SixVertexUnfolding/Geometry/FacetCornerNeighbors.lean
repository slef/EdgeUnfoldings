import SixVertexUnfolding.Geometry.QuadrilateralEdges
import SixVertexUnfolding.Geometry.TriangularFacets
import SixVertexUnfolding.Geometry.FacetCoordinates

/-! At a corner of a triangular or quadrilateral face, precisely two
original edges run along that face. This uses no global graph model. -/

namespace SixVertexUnfolding.ConvexPolyhedron.Face

open Set

variable {P : ConvexPolyhedron} {F : P.Face}

theorem Quadrilateral.corner_neighbors (Q : F.Quadrilateral) (i : Fin 4)
    (w : P.Vertex) (on_face : (w : Space) ∈ F.val) :
    P.edgeGraph.Adj (Q.corner i) w ↔ w = Q.corner (i + 1) ∨ w = Q.corner (i + 3) := by
  obtain ⟨j, same⟩ := Q.vertices ▸ (show (w : Space) ∈ F.val ∩ (P.vertices : Set Space)
    from ⟨on_face, w.property⟩)
  have equal : Q.corner j = w := Subtype.ext same
  rw [← equal, Q.adjacent_iff_consecutive]
  simp only [Q.distinct.eq_iff]
  fin_cases i <;> fin_cases j <;> decide

/-- An incident edge determines the other edge of the same face at the corner. -/
theorem exists_other_corner_neighbor (F : P.Face)
    (small : (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4)
    (pole b : P.Vertex) (edge : P.edgeGraph.Adj pole b)
    (poleF : (pole : Space) ∈ F.val) (bF : (b : Space) ∈ F.val) :
    ∃ c : P.Vertex, c ≠ b ∧ P.edgeGraph.Adj pole c ∧ (c : Space) ∈ F.val ∧
      ∀ w : P.Vertex, (w : Space) ∈ F.val → P.edgeGraph.Adj pole w → w = b ∨ w = c := by
  rcases small with triangle | quadrilateral
  · obtain ⟨c, cp, cb, vertices⟩ := F.exists_third_vertex triangle pole b edge.ne poleF bF
    have cF : (c : Space) ∈ F.val := by
      have member : (c : Space) ∈ F.val ∩ (P.vertices : Set Space) := by rw [vertices]; simp
      exact member.1
    refine ⟨c, cb, F.adjacent_of_triangle triangle pole c cp.symm poleF cF, cF, ?_⟩
    intro w wF adjacent
    have member : (w : Space) ∈ ({(pole : Space), (b : Space), (c : Space)} : Set Space) :=
      vertices ▸ ⟨wF, w.property⟩
    rcases member with same | same | same
    · exact (adjacent.ne (Subtype.ext same.symm)).elim
    · exact Or.inl (Subtype.ext same)
    · exact Or.inr (Subtype.ext same)
  · obtain ⟨Q⟩ := F.exists_quadrilateral quadrilateral
    obtain ⟨i, same⟩ := Q.vertices ▸
      (show (pole : Space) ∈ F.val ∩ (P.vertices : Set Space) from ⟨poleF, pole.property⟩)
    have equal : Q.corner i = pole := Subtype.ext same
    have neighbors := Q.corner_neighbors i b bF
    rw [equal] at neighbors
    have distinct : Q.corner (i + 1) ≠ Q.corner (i + 3) :=
      Q.distinct.ne ((by decide : ∀ i : Fin 4, i + 1 ≠ i + 3) i)
    have left_edge : P.edgeGraph.Adj pole (Q.corner (i + 1)) := equal ▸ Q.consecutive_adjacent i
    have right_edge : P.edgeGraph.Adj pole (Q.corner (i + 3)) := by
      rw [← equal]
      exact (Q.corner_neighbors i _ (Q.corner_mem _)).mpr (Or.inr rfl)
    have exhaust (w : P.Vertex) (wF : (w : Space) ∈ F.val) (adjacent : P.edgeGraph.Adj pole w) :
        w = Q.corner (i + 1) ∨ w = Q.corner (i + 3) :=
      (Q.corner_neighbors i w wF).mp (equal.symm ▸ adjacent)
    rcases neighbors.mp edge with first | last
    · refine ⟨Q.corner (i + 3), by simpa only [first] using distinct.symm,
        right_edge, Q.corner_mem _, ?_⟩
      intro w wF adjacent
      simpa only [first] using exhaust w wF adjacent
    · refine ⟨Q.corner (i + 1), by rwa [last], left_edge, Q.corner_mem _, ?_⟩
      intro w wF adjacent
      simpa only [last, or_comm] using exhaust w wF adjacent

/-- Every corner of a small face has an incident original edge in that face. -/
theorem exists_corner_edge (F : P.Face)
    (small : (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4)
    (pole : P.Vertex) (poleF : (pole : Space) ∈ F.val) :
    ∃ b : P.Vertex, P.edgeGraph.Adj pole b ∧ (b : Space) ∈ F.val := by
  rcases small with triangle | quadrilateral
  · have another : ¬ F.val ∩ (P.vertices : Set Space) ⊆ {(pole : Space)} := by
      intro inclusion
      have bound := Set.ncard_le_ncard inclusion (finite_singleton _)
      rw [triangle, Set.ncard_singleton] at bound
      omega
    obtain ⟨b, bF, different⟩ := Set.not_subset.mp another
    let vertex : P.Vertex := ⟨b, bF.2⟩
    exact ⟨vertex, F.adjacent_of_triangle triangle pole vertex
      (fun same => different (congrArg Subtype.val same).symm) poleF bF.1, bF.1⟩
  · obtain ⟨Q⟩ := F.exists_quadrilateral quadrilateral
    obtain ⟨i, same⟩ := Q.vertices ▸
      (show (pole : Space) ∈ F.val ∩ (P.vertices : Set Space) from ⟨poleF, pole.property⟩)
    exact ⟨Q.corner (i + 1), (Subtype.ext same : Q.corner i = pole) ▸ Q.consecutive_adjacent i,
      Q.corner_mem _⟩

/-- Two facets containing the same three distinct original vertices coincide. -/
theorem eq_of_three_vertices (F G : P.Face) (a b c : P.Vertex)
    (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c)
    (aF : (a : Space) ∈ F.val) (bF : (b : Space) ∈ F.val) (cF : (c : Space) ∈ F.val)
    (aG : (a : Space) ∈ G.val) (bG : (b : Space) ∈ G.val) (cG : (c : Space) ∈ G.val) : F = G := by
  have noncollinear := P.no_three_collinear_vertices a.property b.property c.property
    (fun same => ab (Subtype.ext same)) (fun same => ac (Subtype.ext same))
    (fun same => bc (Subtype.ext same))
  exact F.eq_of_affineSpan_eq G
    ((F.triangle_spans_plane a b c aF bF cF noncollinear).symm.trans
      (G.triangle_spans_plane a b c aG bG cG noncollinear))

end SixVertexUnfolding.ConvexPolyhedron.Face
