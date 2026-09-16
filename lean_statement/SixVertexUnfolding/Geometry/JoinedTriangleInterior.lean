import SixVertexUnfolding.Geometry.TriangleEdgeHalfplanes

/-! The open common base of two oppositely oriented triangles lies inside their union. -/

namespace SixVertexUnfolding

/-- Signed edge height is affine along a segment. -/
theorem segment_weighted_area (e f a b x : Plane) (s t : ℝ)
    (total : s + t = 1) (expression : s • a + t • b = x) :
    det (f - e) (x - e) = s * det (f - e) (a - e) + t * det (f - e) (b - e) := by
  have shifted : s • a + t • b - e = s • (a - e) + t • (b - e) := by
    rw [show s = 1 - t by linarith]
    module
  rw [← expression, shifted, det_add_right, det_smul_right, det_smul_right]

/-- A neighborhood across the common diagonal is covered by the two triangles. -/
theorem open_base_in_joined_triangles (a b c d : Plane)
    (above : 0 < det (b - a) (c - a)) (below : det (b - a) (d - a) < 0) :
    openSegment ℝ a b ⊆ interior (convexHull ℝ ({a, b, c} : Set Plane) ∪ convexHull ℝ ({a, b, d} : Set Plane)) := by
  rintro x ⟨s, t, hs, ht, total, expression⟩
  let u : Set Plane := {y | 0 < det (c - b) (y - b) ∧ 0 < det (a - c) (y - c) ∧
    0 < det (d - a) (y - a) ∧ 0 < det (b - d) (y - d)}
  have height_continuous (v origin : Plane) : Continuous (fun y : Plane => det v (y - origin)) :=
    (detHeight v).continuous.comp (continuous_id.sub continuous_const)
  have open_u : IsOpen u := (isOpen_lt continuous_const (height_continuous _ _)).inter
    ((isOpen_lt continuous_const (height_continuous _ _)).inter
      ((isOpen_lt continuous_const (height_continuous _ _)).inter (isOpen_lt continuous_const (height_continuous _ _))))
  have inside_union : u ⊆ convexHull ℝ ({a, b, c} : Set Plane) ∪ convexHull ℝ ({a, b, d} : Set Plane) := by
    intro y h
    by_cases base_side : 0 ≤ det (b - a) (y - a)
    · exact Or.inl (triangle_mem_of_edge_sides a b c y above base_side h.1.le h.2.1.le)
    · have other : y ∈ convexHull ℝ ({a, d, b} : Set Plane) := by
        apply triangle_mem_of_edge_sides a d b y
        · rw [det_swap]; exact neg_pos.mpr below
        · exact h.2.2.1.le
        · exact h.2.2.2.le
        · have reversed : det (a - b) (y - b) = -det (b - a) (y - a) := by
            simp only [det, PiLp.sub_apply]; ring
          rw [reversed]
          exact neg_nonneg.mpr (le_of_not_ge base_side)
      right
      convert other using 1
      congr 1
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
  have zero (v : Plane) : det v 0 = 0 := by simp [det]
  have ca_b : det (a - c) (b - c) = det (b - a) (c - a) := by
    simp only [det, PiLp.sub_apply]; ring
  have db_a : det (b - d) (a - d) = -det (b - a) (d - a) := by
    simp only [det, PiLp.sub_apply]; ring
  have member : x ∈ u := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [segment_weighted_area b c a b x s t total expression, triangle_area_cycle,
        sub_self, zero, mul_zero, add_zero]
      exact mul_pos hs above
    · rw [segment_weighted_area c a a b x s t total expression, det_self,
        mul_zero, zero_add, ca_b]
      exact mul_pos ht above
    · rw [segment_weighted_area a d a b x s t total expression, sub_self, zero,
        mul_zero, zero_add, det_swap]
      exact mul_pos ht (neg_pos.mpr below)
    · rw [segment_weighted_area d b a b x s t total expression, det_self,
        mul_zero, add_zero, db_a]
      exact mul_pos hs (neg_pos.mpr below)
  exact mem_interior.mpr ⟨u, inside_union, open_u, member⟩

/-- The same interior statement holds for either orientation of the diagonal. -/
theorem open_base_in_joined_triangles_of_opposite (a b c d : Plane)
    (opposite : det (b - a) (c - a) * det (b - a) (d - a) < 0) :
    openSegment ℝ a b ⊆ interior (convexHull ℝ ({a, b, c} : Set Plane) ∪ convexHull ℝ ({a, b, d} : Set Plane)) := by
  rcases mul_neg_iff.mp opposite with ⟨above, below⟩ | ⟨below, above⟩
  · exact open_base_in_joined_triangles a b c d above below
  · simpa only [Set.union_comm] using open_base_in_joined_triangles a b d c above below

end SixVertexUnfolding
