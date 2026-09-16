import SixVertexUnfolding.Geometry.QuadrilateralVertices

/-! A convex quadrilateral is exactly the union of the two triangles along either diagonal. -/

namespace SixVertexUnfolding

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Splitting a closed segment at one of its points preserves the entire closed segment. -/
theorem segment_split_at (a b q : E) (member : q ∈ segment ℝ a b) :
    segment ℝ a b = segment ℝ a q ∪ segment ℝ q b := by
  have on_line : q ∈ Set.range (AffineMap.lineMap a b : ℝ → E) := by
    rw [segment_eq_image_lineMap] at member
    obtain ⟨t, _, rfl⟩ := member
    exact Set.mem_range_self _
  apply Set.Subset.antisymm
  · intro x hx
    rw [← insert_endpoints_openSegment] at hx
    rcases hx with rfl | rfl | middle
    · exact Or.inl (left_mem_segment ℝ _ _)
    · exact Or.inr (right_mem_segment ℝ _ _)
    · rcases openSegment_subset_union a b on_line middle with rfl | left | right
      · exact Or.inl (right_mem_segment ℝ _ _)
      · exact Or.inl (openSegment_subset_segment ℝ a q left)
      · exact Or.inr (openSegment_subset_segment ℝ q b right)
  · exact Set.union_subset ((convex_segment a b).segment_subset (left_mem_segment ℝ a b) member)
      ((convex_segment a b).segment_subset member (right_mem_segment ℝ a b))

/-- Crossing diagonals justify the usual two-triangle decomposition, including all boundaries. -/
theorem quadrilateral_split (a b c d q : E)
    (on_ac : q ∈ segment ℝ a c) (on_bd : q ∈ segment ℝ b d) :
    convexHull ℝ ({a, b, c, d} : Set E) =
      convexHull ℝ ({a, b, c} : Set E) ∪ convexHull ℝ ({a, c, d} : Set E) := by
  have ac_left : segment ℝ a c ⊆ convexHull ℝ ({a, b, c} : Set E) := by
    rw [← convexHull_pair]
    apply convexHull_mono
    intro x hx
    rcases hx with rfl | rfl <;> simp
  have ac_right : segment ℝ a c ⊆ convexHull ℝ ({a, c, d} : Set E) := by
    rw [← convexHull_pair]
    apply convexHull_mono
    intro x hx
    rcases hx with rfl | rfl <;> simp
  have reordered : ({a, b, c, d} : Set E) = {a, c, b, d} := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  apply Set.Subset.antisymm
  · rw [reordered, ← convexJoin_segments, segment_split_at b d q on_bd, convexJoin_union_right]
    apply Set.union_subset
    · apply Set.Subset.trans _ Set.subset_union_left
      apply convexJoin_subset ac_left _ (convex_convexHull ℝ _)
      exact (convex_convexHull ℝ _).segment_subset (subset_convexHull ℝ _ (by simp)) (ac_left on_ac)
    · apply Set.Subset.trans _ Set.subset_union_right
      apply convexJoin_subset ac_right _ (convex_convexHull ℝ _)
      exact (convex_convexHull ℝ _).segment_subset (ac_right on_ac) (subset_convexHull ℝ _ (by simp))
  · apply Set.union_subset <;> apply convexHull_mono
    · intro x hx
      rcases hx with rfl | rfl | rfl <;> simp
    · intro x hx
      rcases hx with rfl | rfl | rfl <;> simp

namespace ConvexPolyhedron.Face.Quadrilateral

variable {P : ConvexPolyhedron} {F : P.Face} (Q : F.Quadrilateral)

/-- An auxiliary diagonal splits this whole original quadrilateral into two closed triangles. -/
theorem face_eq_two_triangles : F.val =
    convexHull ℝ ({(Q.corner 0 : Space), (Q.corner 1 : Space), (Q.corner 2 : Space)} : Set Space) ∪
    convexHull ℝ ({(Q.corner 0 : Space), (Q.corner 2 : Space), (Q.corner 3 : Space)} : Set Space) := by
  obtain ⟨q, on_ac, on_bd⟩ := Q.crossing
  rw [F.eq_convexHull_vertices, Q.vertices]
  have corners : Set.range (fun i => (Q.corner i : Space)) =
      ({(Q.corner 0 : Space), (Q.corner 1 : Space), (Q.corner 2 : Space), (Q.corner 3 : Space)} : Set Space) := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl | rfl | rfl)
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩]
  rw [corners]
  exact quadrilateral_split _ _ _ _ q (openSegment_subset_segment ℝ _ _ on_ac)
    (openSegment_subset_segment ℝ _ _ on_bd)

end ConvexPolyhedron.Face.Quadrilateral
end SixVertexUnfolding
