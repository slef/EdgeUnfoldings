import SixVertexUnfolding.Geometry.JoinedTriangleInterior
import SixVertexUnfolding.Geometry.TriangleBoundary

/-! The frontier of a joined pair has no extra edge along its internal diagonal. -/

namespace SixVertexUnfolding

/-- A nonzero determinant excludes a collinear triangle. -/
theorem noncollinear_of_triangle_det_ne_zero (a b c : Plane)
    (nonzero : det (b - a) (c - a) ≠ 0) : ¬ Collinear ℝ ({a, b, c} : Set Plane) := by
  intro collinear
  obtain ⟨v, along⟩ := (collinear_iff_of_mem (by simp : a ∈ ({a, b, c} : Set Plane))).mp collinear
  obtain ⟨s, hb⟩ := along b (by simp)
  obtain ⟨t, hc⟩ := along c (by simp)
  change b = s • v + a at hb
  change c = t • v + a at hc
  apply nonzero
  rw [hb, hc, add_sub_cancel_right, add_sub_cancel_right, det_smul_left, det_smul_right, det_self, mul_zero, mul_zero]

/-- Only the four outer sides can occur on the frontier of the union. -/
theorem joined_triangles_frontier_subset (a b c d : Plane)
    (opposite : det (b - a) (c - a) * det (b - a) (d - a) < 0) :
    frontier (convexHull ℝ ({a, b, c} : Set Plane) ∪ convexHull ℝ ({a, b, d} : Set Plane)) ⊆
      segment ℝ a c ∪ segment ℝ b c ∪ segment ℝ a d ∪ segment ℝ b d := by
  have c_nonzero : det (b - a) (c - a) ≠ 0 := fun zero => by rw [zero, zero_mul] at opposite; exact lt_irrefl _ opposite
  have d_nonzero : det (b - a) (d - a) ≠ 0 := fun zero => by rw [zero, mul_zero] at opposite; exact lt_irrefl _ opposite
  intro x boundary
  have base_excluded (on_base : x ∈ segment ℝ a b) :
      x ∈ segment ℝ a c ∪ segment ℝ b c ∪ segment ℝ a d ∪ segment ℝ b d := by
    rw [← insert_endpoints_openSegment] at on_base
    rcases on_base with rfl | rfl | on_open_base
    · exact Or.inl (Or.inl (Or.inl (left_mem_segment ℝ _ c)))
    · exact Or.inl (Or.inl (Or.inr (left_mem_segment ℝ _ c)))
    · exact False.elim (boundary.2 (open_base_in_joined_triangles_of_opposite a b c d opposite on_open_base))
  rcases frontier_union_subset _ _ boundary with left | right
  · rcases triangle_frontier_subset_edges a b c (noncollinear_of_triangle_det_ne_zero a b c c_nonzero) left.1 with base | ac | bc
    · exact base_excluded base
    · exact Or.inl (Or.inl (Or.inl ac))
    · exact Or.inl (Or.inl (Or.inr bc))
  · rcases triangle_frontier_subset_edges a b d (noncollinear_of_triangle_det_ne_zero a b d d_nonzero) right.2 with base | ad | bd
    · exact base_excluded base
    · exact Or.inl (Or.inr ad)
    · exact Or.inr bd

end SixVertexUnfolding
