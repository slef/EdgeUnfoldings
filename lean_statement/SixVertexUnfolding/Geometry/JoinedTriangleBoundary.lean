import SixVertexUnfolding.Geometry.TriangleEdgeFrontier

/-! The four outer sides are exactly the frontier of two triangles joined across an internal diagonal. -/

namespace SixVertexUnfolding

/-- An open outer side misses the other triangle; closure also includes its endpoints. -/
theorem joined_triangle_outer_side_frontier (a b c d : Plane)
    (opposite : det (b - a) (c - a) * det (b - a) (d - a) < 0) :
    segment ℝ a c ⊆ frontier (convexHull ℝ ({a, b, c} : Set Plane) ∪ convexHull ℝ ({a, b, d} : Set Plane)) := by
  have nonzero : det (b - a) (c - a) ≠ 0 := by
    intro zero
    rw [zero, zero_mul] at opposite
    exact lt_irrefl 0 opposite
  have edge_boundary : segment ℝ a c ⊆ frontier (convexHull ℝ ({a, b, c} : Set Plane)) := by
    have swapped : det (c - a) (b - a) ≠ 0 := by rw [det_swap]; exact neg_ne_zero.mpr nonzero
    simpa only [Set.pair_comm] using triangle_base_subset_frontier a c b swapped
  rw [← closure_openSegment a c]
  apply closure_minimal _ isClosed_frontier
  rintro x ⟨s, t, hs, ht, total, expression⟩
  have on_edge : x ∈ segment ℝ a c := ⟨s, t, hs.le, ht.le, total, expression⟩
  have boundary := edge_boundary on_edge
  have off_other : x ∉ convexHull ℝ ({a, b, d} : Set Plane) := by
    intro other
    have on_base : x ∈ segment ℝ a b := by
      rw [← opposite_triangles_intersection a b c d opposite]
      exact ⟨((Set.toFinite ({a, b, c} : Set Plane)).isCompact_convexHull ℝ).isClosed.frontier_subset boundary, other⟩
    obtain ⟨u, v, hu, hv, sum, combination⟩ := on_base
    have along_base := segment_weighted_area a b a b x u v sum combination
    have along_edge := segment_weighted_area a b a c x s t total expression
    simp only [sub_self, det_zero_right, det_self, mul_zero, add_zero] at along_base
    simp only [sub_self, det_zero_right, mul_zero, zero_add, along_base] at along_edge
    exact (mul_ne_zero ht.ne' nonzero) along_edge.symm
  refine ⟨closure_mono Set.subset_union_left boundary.1, ?_⟩
  intro inside
  have other_closed := ((Set.toFinite ({a, b, d} : Set Plane)).isCompact_convexHull ℝ).isClosed
  have outside : x ∈ interior (convexHull ℝ ({a, b, d} : Set Plane))ᶜ := by
    rw [other_closed.isOpen_compl.interior_eq]
    exact off_other
  exact boundary.2 (interior_union_inter_interior_compl_right_subset ⟨inside, outside⟩)

/-- There are exactly four boundary sides, with no contribution from the diagonal. -/
theorem joined_triangles_frontier_eq (a b c d : Plane)
    (opposite : det (b - a) (c - a) * det (b - a) (d - a) < 0) :
    frontier (convexHull ℝ ({a, b, c} : Set Plane) ∪ convexHull ℝ ({a, b, d} : Set Plane)) =
      segment ℝ a c ∪ segment ℝ b c ∪ segment ℝ a d ∪ segment ℝ b d := by
  apply Set.Subset.antisymm (joined_triangles_frontier_subset a b c d opposite)
  have reversed : det (a - b) (c - b) * det (a - b) (d - b) < 0 := by
    rw [triangle_area_reverse_base a b c, triangle_area_reverse_base a b d, neg_mul_neg]
    exact opposite
  have ac := joined_triangle_outer_side_frontier a b c d opposite
  have bc : segment ℝ b c ⊆ _ := joined_triangle_outer_side_frontier b a c d reversed
  have ad := joined_triangle_outer_side_frontier a b d c (by simpa only [mul_comm] using opposite)
  have bd : segment ℝ b d ⊆ _ := joined_triangle_outer_side_frontier b a d c (by simpa only [mul_comm] using reversed)
  apply Set.union_subset (Set.union_subset (Set.union_subset ac ?_) ?_) ?_
  · simpa only [Set.insert_comm] using bc
  · simpa only [Set.union_comm] using ad
  · simpa only [Set.insert_comm, Set.union_comm] using bd

end SixVertexUnfolding
