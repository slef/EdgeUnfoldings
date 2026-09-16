import SixVertexUnfolding.Geometry.ReflexRadialTriangle

/-! The radial-triangle containment with the opposite orientation. -/

namespace SixVertexUnfolding

/-- The clockwise version of the reflex near-corner containment, with the same closed finite triangle. -/
theorem near_vertex_in_radial_triangle_clockwise (a b p : Plane)
    (fan_side : det a b < 0) (reflex_side : 0 < det a p)
    (noncollinear : ¬ Collinear ℝ ({a, b, 0} : Set Plane))
    (outward : OppositeHingeSides a b 0 p) :
    a ∈ convexHull ℝ ({0, b, p} : Set Plane) := by
  obtain ⟨height, ha, hb, hp⟩ := outward_patch_height a b 0 p noncollinear outward
  simp only [sub_zero] at ha hb hp
  have reversed : 0 < det b a := by rw [det_swap]; linarith
  have identity : det b p • a = det a p • b + det b a • p := by
    ext i
    fin_cases i
    · change det b p * a 0 = det a p * b 0 + det b a * p 0
      simp only [det]
      ring
    · change det b p * a 1 = det a p * b 1 + det b a * p 1
      simp only [det]
      ring
  have heights := congrArg height identity
  simp only [map_smul, map_add, smul_eq_mul] at heights
  have area : 0 < det b p := by
    have positive : 0 < det b p * height a := by
      rw [heights]
      exact add_pos (mul_pos reflex_side hb) (mul_pos reversed hp)
    exact (mul_pos_iff_of_pos_right ha).mp positive
  have different : a ≠ b := by intro same; rw [same, det_self] at fan_side; linarith
  have side := (oppositeHingeSides_iff_det a b 0 p different).mp outward
  have pole_side : det (b - a) (0 - a) = det a b := by
    simp only [det, PiLp.sub_apply, PiLp.zero_apply]
    ring
  rw [pole_side] at side
  have petal_side : 0 ≤ det (b - a) (p - a) := by nlinarith
  have far_side : 0 ≤ det (p - b) (a - b) := by
    have identity : det (p - b) (a - b) = det (b - a) (p - a) := by
      simp only [det, PiLp.sub_apply]
      ring
    rwa [identity]
  exact triangle_mem_of_three_halfplanes b p a area reversed.le reflex_side.le far_side

end SixVertexUnfolding
