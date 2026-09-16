import SixVertexUnfolding.Geometry.TriangleTopology

/-! Two noncollinear segments sharing a corner have no other common point. -/

namespace SixVertexUnfolding

/-- A point off one supporting line prevents the two incident sides from retracing each other. -/
theorem segments_meet_only_at_corner (a b c : Plane)
    (off_line : b ∉ affineSpan ℝ ({a, c} : Set Plane)) (x : Plane)
    (first : x ∈ segment ℝ a b) (second : x ∈ segment ℝ a c) : x = a := by
  by_contra different
  have first_line : x ∈ affineSpan ℝ ({a, b} : Set Plane) :=
    (affineSpan ℝ ({a, b} : Set Plane)).convex.segment_subset
      (left_mem_affineSpan_pair ℝ a b) (right_mem_affineSpan_pair ℝ a b) first
  have second_line : x ∈ affineSpan ℝ ({a, c} : Set Plane) :=
    (affineSpan ℝ ({a, c} : Set Plane)).convex.segment_subset
      (left_mem_affineSpan_pair ℝ a c) (right_mem_affineSpan_pair ℝ a c) second
  have same := (affineSpan_pair_eq_of_right_mem_of_ne first_line different).symm.trans
    (affineSpan_pair_eq_of_right_mem_of_ne second_line different)
  apply off_line
  rw [← same]
  exact right_mem_affineSpan_pair ℝ a b

/-- Off-line placement is unchanged when the distinguished corner is exchanged. -/
theorem off_line_at_other_corner (a b p : Plane) (different : a ≠ b)
    (off_line : p ∉ affineSpan ℝ ({a, b} : Set Plane)) :
    a ∉ affineSpan ℝ ({p, b} : Set Plane) := by
  intro member
  have same := affineSpan_pair_eq_of_left_mem_of_ne member different
  apply off_line
  rw [same]
  exact left_mem_affineSpan_pair ℝ p b

end SixVertexUnfolding
