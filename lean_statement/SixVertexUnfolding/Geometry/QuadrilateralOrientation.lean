import SixVertexUnfolding.Geometry.QuadrilateralRegionBoundary
import SixVertexUnfolding.Geometry.BoundaryTriangleSides

/-! A contained triangle determines the orientation of the four-sided pocket boundary. -/

namespace SixVertexUnfolding

/-- A triangle on the right of the first radial side forces both constituent triangles to run clockwise. -/
theorem quadrilateral_clockwise_of_right_triangle (a p b w c : Plane)
    (diagonal : det (b - a) (p - a) * det (b - a) (w - a) < 0 ∨
      det (w - p) (a - p) * det (w - p) (b - p) < 0)
    (contained : convexHull ℝ ({w, a, c} : Set Plane) ⊆ quadrilateralRegion a p b w)
    (right_side : det (a - w) (c - w) < 0) :
    (0 < det (b - a) (p - a) ∧ det (b - a) (w - a) < 0) ∨
      (det (w - p) (a - p) < 0 ∧ 0 < det (w - p) (b - p)) := by
  have edge : segment ℝ w a ⊆ frontier (quadrilateralRegion a p b w) := by
    rw [quadrilateralRegion_frontier_eq a p b w diagonal]
    exact Set.subset_union_right
  by_cases first : det (b - a) (p - a) * det (b - a) (w - a) < 0
  · have triangle : convexHull ℝ ({w, a, b} : Set Plane) ⊆ quadrilateralRegion a p b w := by
      intro x member
      unfold quadrilateralRegion
      rw [if_pos first]
      right
      apply convexHull_mono _ member
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at *
      tauto
    have same := triangles_on_frontier_same_side _ w a c b edge contained triangle
    have cycle : det (a - w) (b - w) = det (b - a) (w - a) := by simp only [det, PiLp.sub_apply]; ring
    rw [cycle] at same
    rcases mul_neg_iff.mp first with clockwise | backwards
    · exact Or.inl clockwise
    · exact False.elim ((not_lt_of_ge same) (mul_neg_of_neg_of_pos right_side backwards.2))
  · have second := diagonal.resolve_left first
    have triangle : convexHull ℝ ({w, a, p} : Set Plane) ⊆ quadrilateralRegion a p b w := by
      intro x member
      unfold quadrilateralRegion
      rw [if_neg first]
      left
      apply convexHull_mono _ member
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at *
      tauto
    have same := triangles_on_frontier_same_side _ w a c p edge contained triangle
    have cycle : det (a - w) (p - w) = det (w - p) (a - p) := by simp only [det, PiLp.sub_apply]; ring
    rw [cycle] at same
    rcases mul_neg_iff.mp second with backwards | clockwise
    · exact False.elim ((not_lt_of_ge same) (mul_neg_of_neg_of_pos right_side backwards.1))
    · exact Or.inr clockwise

/-- A triangle on the left of the last radial side determines the same clockwise orientation. -/
theorem quadrilateral_clockwise_of_left_triangle (a p b w c : Plane)
    (diagonal : det (b - a) (p - a) * det (b - a) (w - a) < 0 ∨
      det (w - p) (a - p) * det (w - p) (b - p) < 0)
    (contained : convexHull ℝ ({w, b, c} : Set Plane) ⊆ quadrilateralRegion a p b w)
    (left_side : 0 < det (b - w) (c - w)) :
    (0 < det (b - a) (p - a) ∧ det (b - a) (w - a) < 0) ∨
      (det (w - p) (a - p) < 0 ∧ 0 < det (w - p) (b - p)) := by
  have edge : segment ℝ w b ⊆ frontier (quadrilateralRegion a p b w) := by
    rw [quadrilateralRegion_frontier_eq a p b w diagonal]
    exact Set.subset_union_right.trans Set.subset_union_left
  by_cases first : det (b - a) (p - a) * det (b - a) (w - a) < 0
  · have triangle : convexHull ℝ ({w, b, a} : Set Plane) ⊆ quadrilateralRegion a p b w := by
      intro x member
      unfold quadrilateralRegion
      rw [if_pos first]
      right
      apply convexHull_mono _ member
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at *
      tauto
    have same := triangles_on_frontier_same_side _ w b c a edge contained triangle
    have cycle : det (b - w) (a - w) = -det (b - a) (w - a) := by simp only [det, PiLp.sub_apply]; ring
    rw [cycle] at same
    rcases mul_neg_iff.mp first with clockwise | backwards
    · exact Or.inl clockwise
    · exact False.elim ((not_lt_of_ge same) (mul_neg_of_pos_of_neg left_side (neg_neg_of_pos backwards.2)))
  · have second := diagonal.resolve_left first
    have triangle : convexHull ℝ ({w, b, p} : Set Plane) ⊆ quadrilateralRegion a p b w := by
      intro x member
      unfold quadrilateralRegion
      rw [if_neg first]
      right
      apply convexHull_mono _ member
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at *
      tauto
    have same := triangles_on_frontier_same_side _ w b c p edge contained triangle
    have cycle : det (b - w) (p - w) = det (w - p) (b - p) := by simp only [det, PiLp.sub_apply]; ring
    rw [cycle] at same
    rcases mul_neg_iff.mp second with backwards | clockwise
    · exact False.elim ((not_lt_of_ge same) (mul_neg_of_pos_of_neg left_side backwards.2))
    · exact Or.inr clockwise

end SixVertexUnfolding
