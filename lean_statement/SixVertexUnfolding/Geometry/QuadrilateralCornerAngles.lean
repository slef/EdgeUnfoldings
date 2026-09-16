import SixVertexUnfolding.Geometry.FacetCornerAngles

/-! The four actual interior angles of a convex quadrilateral sum to a full turn.
The diagonal splits are justified by the crossing of its open diagonals. -/

namespace SixVertexUnfolding.ConvexPolyhedron.Face.Quadrilateral

open Set Real EuclideanGeometry

variable {P : ConvexPolyhedron} {F : P.Face} (Q : F.Quadrilateral)

/-- A diagonal splits the ordinary interior angle into its two triangle angles. -/
theorem angle_split (i : Fin 4) :
    angle (Q.corner (i + 1) : Space) (Q.corner i) (Q.corner (i + 3)) =
      angle (Q.corner (i + 1) : Space) (Q.corner i) (Q.corner (i + 2)) +
      angle (Q.corner (i + 2) : Space) (Q.corner i) (Q.corner (i + 3)) := by
  have ne (j k : Fin 4) (different : j ≠ k) : (Q.corner j : Space) ≠ Q.corner k :=
    fun same => Q.corner_ne j k different (Subtype.ext same)
  obtain ⟨x, first, second⟩ := Q.cyclic_crossing i
  have ray := mem_segment_iff_wbtw.mp (openSegment_subset_segment ℝ _ _ first)
  have not_start : x ≠ (Q.corner i : Space) := by
    intro same
    rw [same] at first
    exact ne i (i + 2) (by fin_cases i <;> decide) (left_mem_openSegment_iff.mp first)
  have split := angle_add_of_ne_of_ne
    (ne i (i + 1) (by fin_cases i <;> decide))
    (ne i (i + 3) (by fin_cases i <;> decide))
    (mem_segment_iff_wbtw.mp (openSegment_subset_segment ℝ _ _ second))
  rw [ray.angle_eq_right _ not_start, ray.angle_eq_left _ not_start] at split
  exact split.symm

/-- The sum is computed from the two triangles of an actual diagonal. -/
theorem sum_angles :
    (∑ i : Fin 4, angle (Q.corner (i + 1) : Space) (Q.corner i) (Q.corner (i + 3))) = 2 * π := by
  have ne (j k : Fin 4) (different : j ≠ k) : (Q.corner j : Space) ≠ Q.corner k :=
    fun same => Q.corner_ne j k different (Subtype.ext same)
  have first := angle_add_angle_add_angle_eq_pi (Q.corner 2 : Space) (ne 1 0 (by decide))
  have second := angle_add_angle_add_angle_eq_pi (Q.corner 3 : Space) (ne 2 0 (by decide))
  have split0 := Q.angle_split 0
  have split2 := Q.angle_split 2
  change angle (Q.corner 1 : Space) (Q.corner 0) (Q.corner 3) =
    angle (Q.corner 1 : Space) (Q.corner 0) (Q.corner 2) +
    angle (Q.corner 2 : Space) (Q.corner 0) (Q.corner 3) at split0
  change angle (Q.corner 3 : Space) (Q.corner 2) (Q.corner 1) =
    angle (Q.corner 3 : Space) (Q.corner 2) (Q.corner 0) +
    angle (Q.corner 0 : Space) (Q.corner 2) (Q.corner 1) at split2
  simp only [Fin.sum_univ_succ]
  change angle (Q.corner 1 : Space) (Q.corner 0) (Q.corner 3) +
    (angle (Q.corner 2 : Space) (Q.corner 1) (Q.corner 0) +
      (angle (Q.corner 3 : Space) (Q.corner 2) (Q.corner 1) +
        (angle (Q.corner 0 : Space) (Q.corner 3) (Q.corner 2) + 0))) = 2 * π
  linarith [angle_comm (Q.corner 0 : Space) (Q.corner 1) (Q.corner 2),
    angle_comm (Q.corner 1 : Space) (Q.corner 2) (Q.corner 0),
    angle_comm (Q.corner 2 : Space) (Q.corner 0) (Q.corner 1),
    angle_comm (Q.corner 0 : Space) (Q.corner 2) (Q.corner 3),
    angle_comm (Q.corner 2 : Space) (Q.corner 3) (Q.corner 0),
    angle_comm (Q.corner 3 : Space) (Q.corner 0) (Q.corner 2)]

end SixVertexUnfolding.ConvexPolyhedron.Face.Quadrilateral
