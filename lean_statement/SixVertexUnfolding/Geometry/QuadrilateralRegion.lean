import SixVertexUnfolding.Geometry.QuadrilateralDiagonal
import SixVertexUnfolding.Geometry.JoinedTriangleFrontier

/-! A concrete pocket region, formed from the two triangles along a separating diagonal. -/

namespace SixVertexUnfolding

/-- Use the base diagonal when it separates the other corners; otherwise use the contact-to-pole diagonal. -/
noncomputable def quadrilateralRegion (a p b w : Plane) : Set Plane :=
  if det (b - a) (p - a) * det (b - a) (w - a) < 0 then
    convexHull ℝ ({a, b, p} : Set Plane) ∪ convexHull ℝ ({a, b, w} : Set Plane)
  else convexHull ℝ ({p, w, a} : Set Plane) ∪ convexHull ℝ ({p, w, b} : Set Plane)

/-- The finite triangle union is compact in either branch. -/
theorem quadrilateralRegion_compact (a p b w : Plane) : IsCompact (quadrilateralRegion a p b w) := by
  unfold quadrilateralRegion
  split_ifs <;> exact (Set.toFinite _).isCompact_convexHull ℝ |>.union ((Set.toFinite _).isCompact_convexHull ℝ)

/-- The chosen region stays within the convex hull of its four named corners. -/
theorem quadrilateralRegion_subset_hull (a p b w : Plane) :
    quadrilateralRegion a p b w ⊆ convexHull ℝ ({a, p, b, w} : Set Plane) := by
  unfold quadrilateralRegion
  split_ifs <;> apply Set.union_subset <;> apply convexHull_mono <;>
    intro x member <;> simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at * <;> tauto

/-- An actual separating diagonal makes the open region nonempty. -/
theorem quadrilateralRegion_interior_nonempty (a p b w : Plane)
    (diagonal : det (b - a) (p - a) * det (b - a) (w - a) < 0 ∨
      det (w - p) (a - p) * det (w - p) (b - p) < 0) :
    (interior (quadrilateralRegion a p b w)).Nonempty := by
  unfold quadrilateralRegion
  split_ifs with first
  · have nonzero : det (b - a) (p - a) ≠ 0 := fun zero => by rw [zero, zero_mul] at first; exact lt_irrefl _ first
    exact (planar_triangle_interior_nonempty a b p (noncollinear_of_triangle_det_ne_zero a b p nonzero)).mono
      (interior_mono Set.subset_union_left)
  · have second := diagonal.resolve_left first
    have nonzero : det (w - p) (a - p) ≠ 0 := fun zero => by rw [zero, zero_mul] at second; exact lt_irrefl _ second
    exact (planar_triangle_interior_nonempty p w a (noncollinear_of_triangle_det_ne_zero p w a nonzero)).mono
      (interior_mono Set.subset_union_left)

/-- The entire frontier is covered by the original four sides; the diagonal is internal. -/
theorem quadrilateralRegion_frontier_subset (a p b w : Plane)
    (diagonal : det (b - a) (p - a) * det (b - a) (w - a) < 0 ∨
      det (w - p) (a - p) * det (w - p) (b - p) < 0) :
    frontier (quadrilateralRegion a p b w) ⊆
      segment ℝ a p ∪ segment ℝ p b ∪ segment ℝ w b ∪ segment ℝ w a := by
  unfold quadrilateralRegion
  split_ifs with first
  · simpa only [segment_symm ℝ b p, segment_symm ℝ a w, segment_symm ℝ b w,
      Set.union_assoc, Set.union_comm, Set.union_left_comm] using joined_triangles_frontier_subset a b p w first
  · simpa only [segment_symm ℝ p a, Set.union_assoc, Set.union_comm, Set.union_left_comm] using
      joined_triangles_frontier_subset p w a b (diagonal.resolve_left first)

/-- A height bound on the four vertices controls the whole compact region. -/
theorem quadrilateralRegion_below (a p b w : Plane) (height : Plane →ᵃ[ℝ] ℝ) (level : ℝ)
    (ha : height a < level) (hp : height p < level) (hb : height b < level) (hw : height w < level) :
    quadrilateralRegion a p b w ⊆ {x | height x < level} := by
  apply (quadrilateralRegion_subset_hull a p b w).trans
  apply convexHull_min _ ((convex_Iio level).affine_preimage height)
  rintro x (rfl | rfl | rfl | rfl)
  exacts [ha, hp, hb, hw]

end SixVertexUnfolding
