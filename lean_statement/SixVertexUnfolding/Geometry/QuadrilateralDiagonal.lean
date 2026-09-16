import SixVertexUnfolding.Geometry.QuadrilateralBoundary
import SixVertexUnfolding.Geometry.SegmentCrossing

/-! Every nondegenerate candidate quadrilateral has a diagonal separating its other two corners. -/

namespace SixVertexUnfolding

/-- The oriented version: failure of both diagonal tests forces a forbidden side crossing. -/
theorem separating_diagonal_of_positive_area (a p b w : Plane)
    (left : Disjoint (segment ℝ a p) (segment ℝ w b))
    (right : Disjoint (segment ℝ p b) (segment ℝ w a))
    (positive : 0 < det (b - a) (p - a))
    (left_nonzero : det (w - p) (a - p) ≠ 0)
    (right_nonzero : det (w - p) (b - p) ≠ 0) :
    det (b - a) (p - a) * det (b - a) (w - a) < 0 ∨
      det (w - p) (a - p) * det (w - p) (b - p) < 0 := by
  let A := det (b - a) (p - a)
  let B := det (b - a) (w - a)
  let C := det (w - p) (a - p)
  let D := det (w - p) (b - p)
  change 0 < A at positive
  change C ≠ 0 at left_nonzero
  change D ≠ 0 at right_nonzero
  change A * B < 0 ∨ C * D < 0
  by_cases first : A * B < 0
  · exact Or.inl first
  right
  by_contra second
  have B_nonneg : 0 ≤ B := by nlinarith
  have product_nonneg : 0 ≤ C * D := le_of_not_gt second
  have ap_b : det (p - a) (b - a) = -A := det_swap _ _
  have ap_w : det (p - a) (w - a) = C := by
    dsimp [C]; simp only [det, PiLp.sub_apply]; ring
  have bw_a : det (w - b) (a - b) = B := by
    dsimp [B]; simp only [det, PiLp.sub_apply]; ring
  have bw_p : det (w - b) (p - b) = -D := by
    dsimp [D]; simp only [det, PiLp.sub_apply]; ring
  have pb_a : det (b - p) (a - p) = -A := by
    dsimp [A]; simp only [det, PiLp.sub_apply]; ring
  have pb_w : det (b - p) (w - p) = -D := det_swap _ _
  have aw_p : det (w - a) (p - a) = -C := by
    dsimp [C]; simp only [det, PiLp.sub_apply]; ring
  have aw_b : det (w - a) (b - a) = -B := det_swap _ _
  rcases lt_or_gt_of_ne left_nonzero with C_negative | C_positive
  · have D_nonpos : D ≤ 0 := by nlinarith
    have D_negative : D < 0 := lt_of_le_of_ne D_nonpos right_nonzero
    obtain ⟨x, first_side, second_side⟩ := closed_segments_meet_of_sides p b a w
      (by rw [pb_a]; linarith) (by rw [pb_w]; linarith)
      (by rw [aw_p]; linarith) (by rw [aw_b]; linarith)
    exact Set.disjoint_left.mp right first_side (by rwa [segment_symm] at second_side)
  · have D_nonneg : 0 ≤ D := by nlinarith
    obtain ⟨x, first_side, second_side⟩ := closed_segments_meet_of_sides a p b w
      (by rw [ap_b]; linarith) (by rw [ap_w]; exact C_positive)
      (by rw [bw_a]; exact B_nonneg) (by rw [bw_p]; linarith)
    exact Set.disjoint_left.mp left first_side (by rwa [segment_symm] at second_side)

/-- The diagonal alternative is independent of the chosen orientation of the plane. -/
theorem separating_diagonal_of_nonzero_areas (a p b w : Plane)
    (left : Disjoint (segment ℝ a p) (segment ℝ w b))
    (right : Disjoint (segment ℝ p b) (segment ℝ w a))
    (base_nonzero : det (b - a) (p - a) ≠ 0)
    (left_nonzero : det (w - p) (a - p) ≠ 0)
    (right_nonzero : det (w - p) (b - p) ≠ 0) :
    det (b - a) (p - a) * det (b - a) (w - a) < 0 ∨
      det (w - p) (a - p) * det (w - p) (b - p) < 0 := by
  rcases lt_or_gt_of_ne base_nonzero with negative | positive
  · have reverse_area (x : Plane) : det (a - b) (x - b) = -det (b - a) (x - a) := by
      simp only [det, PiLp.sub_apply]; ring
    have reversed := separating_diagonal_of_positive_area b p a w
      (by rwa [segment_symm ℝ b p]) (by rwa [segment_symm ℝ p a])
      (by rw [reverse_area]; linarith) right_nonzero left_nonzero
    simpa only [reverse_area, neg_mul_neg, mul_comm] using reversed
  · exact separating_diagonal_of_positive_area a p b w left right positive left_nonzero right_nonzero

/-- A generic point off a line of distinct endpoints gives a nonzero triangle determinant. -/
theorem triangle_det_ne_zero_of_off_line (a b p : Plane) (different : a ≠ b)
    (off_line : p ∉ affineSpan ℝ ({a, b} : Set Plane)) : det (b - a) (p - a) ≠ 0 := by
  apply det_ne_zero_of_noncollinear
  intro collinear
  exact off_line (collinear.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) different)

/-- The actual boundary certificate and generic-point conditions supply an internal diagonal. -/
theorem QuadrilateralBoundary.separating_diagonal {a p b w : Plane}
    (boundary : QuadrilateralBoundary a p b w)
    (off_base : p ∉ affineSpan ℝ ({a, b} : Set Plane))
    (off_left : p ∉ affineSpan ℝ ({a, w} : Set Plane))
    (off_right : p ∉ affineSpan ℝ ({b, w} : Set Plane)) :
    det (b - a) (p - a) * det (b - a) (w - a) < 0 ∨
      det (w - p) (a - p) * det (w - p) (b - p) < 0 := by
  obtain ⟨_, ab, aw, _, _, bw⟩ := boundary.corners_distinct
  have left_area := triangle_det_ne_zero_of_off_line a w p aw off_left
  have right_area := triangle_det_ne_zero_of_off_line b w p bw off_right
  have rotated (x : Plane) : det (w - p) (x - p) = -det (w - x) (p - x) := by
    simp only [det, PiLp.sub_apply]; ring
  apply separating_diagonal_of_nonzero_areas a p b w boundary.opposite_left boundary.opposite_right
    (triangle_det_ne_zero_of_off_line a b p ab off_base)
  · rw [rotated]; exact neg_ne_zero.mpr left_area
  · rw [rotated]; exact neg_ne_zero.mpr right_area

end SixVertexUnfolding
