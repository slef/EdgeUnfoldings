import SixVertexUnfolding.Geometry.JoinedTriangleFrontier
import SixVertexUnfolding.Geometry.TriangleTopology

/-! The diagonal is a common center for paths through the joined triangles. -/

namespace SixVertexUnfolding

open scoped Pointwise

/-- A region star-convex about an interior point has a star-convex interior. -/
theorem planar_starConvex_interior (region : Set Plane) (center : Plane)
    (star : StarConvex ℝ center region) (inside : center ∈ interior region) :
    StarConvex ℝ center (interior region) := by
  intro y member a b ha hb total
  by_cases zero : b = 0
  · have one : a = 1 := by linarith
    simpa only [zero, one, one_smul, zero_smul, add_zero] using inside
  · have scaled : b • y ∈ interior (b • region) := by
      rw [interior_smul₀ zero]
      exact Set.smul_mem_smul_set member
    have added : a • center + b • y ∈ interior (a • ({center} : Set Plane) + b • region) :=
      subset_interior_add_right (Set.add_mem_add (Set.smul_mem_smul_set (Set.mem_singleton center)) scaled)
    exact interior_mono ((starConvex_iff_pointwise_add_subset.mp star) ha hb total) added

/-- Paths between interior points may pass through the midpoint of the internal diagonal. -/
theorem joined_triangles_interior_pathConnected (a b c d : Plane)
    (opposite : det (b - a) (c - a) * det (b - a) (d - a) < 0) :
    IsPathConnected (interior (convexHull ℝ ({a, b, c} : Set Plane) ∪ convexHull ℝ ({a, b, d} : Set Plane))) := by
  let center : Plane := (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b
  have on_base : center ∈ openSegment ℝ a b := ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
  have inside := open_base_in_joined_triangles_of_opposite a b c d opposite on_base
  have in_left : center ∈ convexHull ℝ ({a, b, c} : Set Plane) :=
    (convex_convexHull ℝ _).segment_subset (subset_convexHull ℝ _ (by simp))
      (subset_convexHull ℝ _ (by simp)) (openSegment_subset_segment ℝ a b on_base)
  have in_right : center ∈ convexHull ℝ ({a, b, d} : Set Plane) :=
    (convex_convexHull ℝ _).segment_subset (subset_convexHull ℝ _ (by simp))
      (subset_convexHull ℝ _ (by simp)) (openSegment_subset_segment ℝ a b on_base)
  have star := ((convex_convexHull ℝ _).starConvex in_left).union
    ((convex_convexHull ℝ _).starConvex in_right)
  exact (planar_starConvex_interior _ center star inside).isPathConnected inside

/-- No boundary pieces are left outside the closure of the joined interior. -/
theorem joined_triangles_regular (a b c d : Plane)
    (opposite : det (b - a) (c - a) * det (b - a) (d - a) < 0) :
    closure (interior (convexHull ℝ ({a, b, c} : Set Plane) ∪ convexHull ℝ ({a, b, d} : Set Plane))) =
      convexHull ℝ ({a, b, c} : Set Plane) ∪ convexHull ℝ ({a, b, d} : Set Plane) := by
  have left_closed := ((Set.toFinite ({a, b, c} : Set Plane)).isCompact_convexHull ℝ).isClosed
  have right_closed := ((Set.toFinite ({a, b, d} : Set Plane)).isCompact_convexHull ℝ).isClosed
  have nonzero : det (b - a) (c - a) ≠ 0 ∧ det (b - a) (d - a) ≠ 0 := by
    constructor <;> intro zero <;> rw [zero] at opposite <;> simp at opposite
  have left_regular := planar_triangle_regular a b c (noncollinear_of_triangle_det_ne_zero a b c nonzero.1)
  have right_regular := planar_triangle_regular a b d (noncollinear_of_triangle_det_ne_zero a b d nonzero.2)
  apply Set.Subset.antisymm
  · exact (closure_mono interior_subset).trans_eq (left_closed.union right_closed).closure_eq
  · apply Set.union_subset
    · calc
        convexHull ℝ ({a, b, c} : Set Plane) = closure (interior (convexHull ℝ ({a, b, c} : Set Plane))) := left_regular.symm
        _ ⊆ _ := closure_mono (interior_mono Set.subset_union_left)
    · calc
        convexHull ℝ ({a, b, d} : Set Plane) = closure (interior (convexHull ℝ ({a, b, d} : Set Plane))) := right_regular.symm
        _ ⊆ _ := closure_mono (interior_mono Set.subset_union_right)

end SixVertexUnfolding
