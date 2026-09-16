import SixVertexUnfolding.Geometry.TriangleHalfplanes
import SixVertexUnfolding.Geometry.OutwardPatch

/-! A reflex near corner of an outward patch lies in the triangle of its other three corners. -/

namespace SixVertexUnfolding

/-- Signed sides express the reflex corner; the outward hinge supplies the third finite-triangle inequality. -/
theorem near_vertex_in_radial_triangle (a b p : Plane)
    (fan_side : 0 < det a b) (reflex_side : det a p < 0)
    (noncollinear : ¬ Collinear ℝ ({a, b, 0} : Set Plane))
    (outward : OppositeHingeSides a b 0 p) :
    a ∈ convexHull ℝ ({0, b, p} : Set Plane) := by
  obtain ⟨height, ha, hb, hp⟩ := outward_patch_height a b 0 p noncollinear outward
  simp only [sub_zero] at ha hb hp
  have reversed : 0 < det p a := by rw [det_swap]; linarith
  have identity : det p b • a = det a b • p + det p a • b := by
    ext i
    fin_cases i
    · change det p b * a 0 = det a b * p 0 + det p a * b 0
      simp only [det]
      ring
    · change det p b * a 1 = det a b * p 1 + det p a * b 1
      simp only [det]
      ring
  have heights := congrArg height identity
  simp only [map_smul, map_add, smul_eq_mul] at heights
  have area : 0 < det p b := by
    have positive : 0 < det p b * height a := by
      rw [heights]
      exact add_pos (mul_pos fan_side hp) (mul_pos reversed hb)
    exact (mul_pos_iff_of_pos_right ha).mp positive
  have different : a ≠ b := by intro same; rw [same, det_self] at fan_side; linarith
  have side := (oppositeHingeSides_iff_det a b 0 p different).mp outward
  have pole_side : det (b - a) (0 - a) = det a b := by
    simp only [det, PiLp.sub_apply, PiLp.zero_apply]
    ring
  rw [pole_side] at side
  have petal_side : det (b - a) (p - a) ≤ 0 := by nlinarith
  have far_side : 0 ≤ det (b - p) (a - p) := by
    have identity : det (b - p) (a - p) = -det (b - a) (p - a) := by
      simp only [det, PiLp.sub_apply]
      ring
    rw [identity]
    exact neg_nonneg.mpr petal_side
  have member := triangle_mem_of_three_halfplanes p b a area reversed.le fan_side.le far_side
  simpa only [Set.pair_comm] using member

end SixVertexUnfolding
