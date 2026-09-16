import SixVertexUnfolding.Geometry.SegmentCorner

/-! A concrete four-sided boundary: opposite sides miss, and adjacent sides meet only at their named corner. -/

namespace SixVertexUnfolding

/-- These six conditions describe the intersections of all pairs of closed sides. -/
structure QuadrilateralBoundary (a p b w : Plane) : Prop where
  opposite_left : Disjoint (segment ℝ a p) (segment ℝ w b)
  opposite_right : Disjoint (segment ℝ p b) (segment ℝ w a)
  at_left : ∀ x ∈ segment ℝ a p, x ∈ segment ℝ a w → x = a
  at_contact : ∀ x ∈ segment ℝ p a, x ∈ segment ℝ p b → x = p
  at_right : ∀ x ∈ segment ℝ b p, x ∈ segment ℝ b w → x = b
  at_pole : ∀ x ∈ segment ℝ w a, x ∈ segment ℝ w b → x = w

/-- The boundary conditions exclude collapsed sides and repeated corners. -/
theorem QuadrilateralBoundary.corners_distinct {a p b w : Plane} (boundary : QuadrilateralBoundary a p b w) :
    a ≠ p ∧ a ≠ b ∧ a ≠ w ∧ p ≠ b ∧ p ≠ w ∧ b ≠ w := by
  have left_ne {x y : Plane} (hx : x ∈ segment ℝ a p) (hy : y ∈ segment ℝ w b) : x ≠ y := by
    rintro rfl
    exact Set.disjoint_left.mp boundary.opposite_left hx hy
  have right_ne {x y : Plane} (hx : x ∈ segment ℝ p b) (hy : y ∈ segment ℝ w a) : x ≠ y := by
    rintro rfl
    exact Set.disjoint_left.mp boundary.opposite_right hx hy
  exact ⟨(right_ne (left_mem_segment ℝ p b) (right_mem_segment ℝ w a)).symm,
    left_ne (left_mem_segment ℝ a p) (right_mem_segment ℝ w b),
    left_ne (left_mem_segment ℝ a p) (left_mem_segment ℝ w b),
    left_ne (right_mem_segment ℝ a p) (right_mem_segment ℝ w b),
    left_ne (right_mem_segment ℝ a p) (left_mem_segment ℝ w b),
    right_ne (right_mem_segment ℝ p b) (left_mem_segment ℝ w a)⟩

/-- The ordered corner list represents four distinct geometric vertices. -/
theorem QuadrilateralBoundary.vertices_injective {a p b w : Plane} (boundary : QuadrilateralBoundary a p b w) :
    Function.Injective ![a, p, b, w] := by
  obtain ⟨ap, ab, aw, pb, pw, bw⟩ := boundary.corners_distinct
  intro i j same
  fin_cases i <;> fin_cases j <;> simp_all

/-- Only three lines need be avoided when the radial sides and opposite sides are already safe. -/
theorem quadrilateralBoundary_of_off_lines (a p b w : Plane)
    (opposite_left : Disjoint (segment ℝ a p) (segment ℝ w b))
    (opposite_right : Disjoint (segment ℝ p b) (segment ℝ w a))
    (radial : ∀ x ∈ segment ℝ w a, x ∈ segment ℝ w b → x = w)
    (off_base : p ∉ affineSpan ℝ ({a, b} : Set Plane))
    (off_left : p ∉ affineSpan ℝ ({a, w} : Set Plane))
    (off_right : p ∉ affineSpan ℝ ({b, w} : Set Plane)) :
    QuadrilateralBoundary a p b w := by
  have different : a ≠ b := by
    intro same
    exact Set.disjoint_left.mp opposite_left (left_mem_segment ℝ a p)
      (same ▸ right_mem_segment ℝ w b)
  exact ⟨opposite_left, opposite_right,
    segments_meet_only_at_corner a p w off_left,
    segments_meet_only_at_corner p a b (off_line_at_other_corner a b p different off_base),
    segments_meet_only_at_corner b p w off_right, radial⟩

end SixVertexUnfolding
