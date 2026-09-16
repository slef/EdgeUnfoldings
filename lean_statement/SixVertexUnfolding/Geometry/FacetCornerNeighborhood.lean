import SixVertexUnfolding.Geometry.FacetCornerNeighbors
import SixVertexUnfolding.Geometry.QuadrilateralSplit

/-! Near a corner, a whole original face is contained in the triangle
formed by that corner and its two original edge neighbors. The far half
of a quadrilateral is excluded by an explicit open neighborhood. -/

namespace SixVertexUnfolding.ConvexPolyhedron.Face

open Set

variable {P : ConvexPolyhedron} {F : P.Face}

theorem Quadrilateral.corner_triangle_neighborhood (Q : F.Quadrilateral) (i : Fin 4) :
    ∃ U : Set Space, IsOpen U ∧ (Q.corner i : Space) ∈ U ∧
      U ∩ F.val ⊆ convexHull ℝ
        ({(Q.corner i : Space), (Q.corner (i + 1) : Space), (Q.corner (i + 3) : Space)} : Set Space) := by
  let remote := convexHull ℝ
    ({(Q.corner (i + 1) : Space), (Q.corner (i + 3) : Space), (Q.corner (i + 2) : Space)} : Set Space)
  have closed : IsClosed remote := (Set.toFinite _).isClosed_convexHull ℝ
  have outside : (Q.corner i : Space) ∉ remote := by
    intro member
    apply P.vertex_not_mem_hull_others (Q.corner i)
    apply convexHull_mono ?_ member
    rintro x (rfl | rfl | rfl)
    all_goals
      refine ⟨(Q.corner _).property, ?_⟩
      intro same
      have impossible := Q.distinct (Subtype.ext same)
      fin_cases i <;> simp_all
  have vertices : F.val ∩ (P.vertices : Set Space) =
      {(Q.corner (i + 1) : Space), (Q.corner i : Space),
        (Q.corner (i + 3) : Space), (Q.corner (i + 2) : Space)} := by
    rw [Q.vertices]
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      fin_cases i <;> fin_cases j <;> simp
    · rintro (rfl | rfl | rfl | rfl)
      all_goals exact mem_range_self _
  obtain ⟨q, pole_diagonal, other_diagonal⟩ := Q.cyclic_crossing i
  have split := quadrilateral_split (Q.corner (i + 1) : Space) (Q.corner i)
    (Q.corner (i + 3)) (Q.corner (i + 2)) q
    (openSegment_subset_segment ℝ _ _ other_diagonal)
    (openSegment_subset_segment ℝ _ _ pole_diagonal)
  refine ⟨remoteᶜ, closed.isOpen_compl, outside, ?_⟩
  rintro x ⟨near, on_face⟩
  rw [F.eq_convexHull_vertices, vertices, split] at on_face
  rcases on_face with triangle | far
  · simpa only [Set.insert_comm] using triangle
  · exact (near far).elim

/-- A corner triangle describes the original face in a neighborhood of its pole. -/
theorem corner_triangle_neighborhood (F : P.Face)
    (small : (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4)
    (pole b c : P.Vertex) (pb : P.edgeGraph.Adj pole b) (pc : P.edgeGraph.Adj pole c)
    (different : b ≠ c) (poleF : (pole : Space) ∈ F.val)
    (bF : (b : Space) ∈ F.val) (cF : (c : Space) ∈ F.val) :
    ∃ U : Set Space, IsOpen U ∧ (pole : Space) ∈ U ∧
      U ∩ F.val ⊆ convexHull ℝ ({(pole : Space), (b : Space), (c : Space)} : Set Space) := by
  rcases small with triangle | quadrilateral
  · have inclusion : ({(pole : Space), (b : Space), (c : Space)} : Set Space) ⊆
        F.val ∩ (P.vertices : Set Space) := by
      rintro x (rfl | rfl | rfl)
      exacts [⟨poleF, pole.property⟩, ⟨bF, b.property⟩, ⟨cF, c.property⟩]
    have equal := Set.eq_of_subset_of_ncard_le inclusion (show
        (F.val ∩ (P.vertices : Set Space)).ncard ≤
          ({(pole : Space), (b : Space), (c : Space)} : Set Space).ncard by
      rw [triangle, Set.ncard_insert_of_notMem (show (pole : Space) ∉
        ({(b : Space), (c : Space)} : Set Space) by
          rintro (same | same)
          · exact pb.ne (Subtype.ext same)
          · exact pc.ne (Subtype.ext same)),
        Set.ncard_pair (fun same => different (Subtype.ext same))])
    refine ⟨univ, isOpen_univ, mem_univ _, ?_⟩
    rintro x ⟨_, member⟩
    rwa [F.eq_convexHull_vertices, ← equal] at member
  · obtain ⟨Q⟩ := F.exists_quadrilateral quadrilateral
    obtain ⟨i, same⟩ := Q.vertices ▸
      (show (pole : Space) ∈ F.val ∩ (P.vertices : Set Space) from ⟨poleF, pole.property⟩)
    have equal : Q.corner i = pole := Subtype.ext same
    have b_side := (Q.corner_neighbors i b bF).mp (equal.symm ▸ pb)
    have c_side := (Q.corner_neighbors i c cF).mp (equal.symm ▸ pc)
    obtain ⟨U, openU, at_pole, contained⟩ := Q.corner_triangle_neighborhood i
    refine ⟨U, openU, equal ▸ at_pole, ?_⟩
    rcases b_side with rfl | rfl <;> rcases c_side with rfl | rfl
    · exact (different rfl).elim
    · simpa only [equal] using contained
    · have swap : ({(pole : Space), (Q.corner (i + 3) : Space),
          (Q.corner (i + 1) : Space)} : Set Space) =
          {(pole : Space), (Q.corner (i + 1) : Space), (Q.corner (i + 3) : Space)} := by
        ext x
        simp only [mem_insert_iff, mem_singleton_iff]
        tauto
      rw [swap]
      simpa only [equal] using contained
    · exact (different rfl).elim

end SixVertexUnfolding.ConvexPolyhedron.Face
