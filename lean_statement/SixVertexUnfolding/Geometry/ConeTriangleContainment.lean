import SixVertexUnfolding.Geometry.TriangleHalfplanes

/-! A cone point cannot escape its finite triangle without its radial segment crossing the opposite side. -/

namespace SixVertexUnfolding

/-- Closed segment avoidance turns angular cone containment into finite triangle containment. -/
theorem triangle_contains_of_cone_and_segment_clear (a b c x : Plane)
    (cone : x - a ∈ twoRayCone (b - a) (c - a))
    (clear : Disjoint (segment ℝ a x) (segment ℝ b c)) :
    x ∈ convexHull ℝ ({a, b, c} : Set Plane) := by
  obtain ⟨s, t, hs, ht, expression⟩ := cone
  by_cases within : s + t ≤ 1
  · apply triangle_mem_of_weights a b c x (1 - s - t) s t (by linarith) hs ht (by ring)
    have position := congrArg (fun y : Plane => y + a) expression
    simp only [sub_add_cancel] at position
    rw [position]
    module
  · have beyond : 1 < s + t := lt_of_not_ge within
    have positive : 0 < s + t := by linarith
    have nonzero := ne_of_gt positive
    let u := s / (s + t)
    let v := t / (s + t)
    have hu : 0 ≤ u := div_nonneg hs positive.le
    have hv : 0 ≤ v := div_nonneg ht positive.le
    have sum : u + v = 1 := by dsimp [u, v]; field_simp
    let z := u • b + v • c
    have in_base : z ∈ segment ℝ b c := ⟨u, v, hu, hv, sum, rfl⟩
    have inverse_nonnegative : 0 ≤ (s + t)⁻¹ := inv_nonneg.mpr positive.le
    have inverse_small : (s + t)⁻¹ ≤ 1 := (inv_le_one₀ positive).mpr beyond.le
    have in_ray : z ∈ segment ℝ a x := by
      refine ⟨1 - (s + t)⁻¹, (s + t)⁻¹, sub_nonneg.mpr inverse_small, inverse_nonnegative, by ring, ?_⟩
      have position := congrArg (fun y : Plane => y + a) expression
      simp only [sub_add_cancel] at position
      rw [position]
      dsimp [z, u, v]
      ext i
      simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
      field_simp
      ring
    exact False.elim (Set.disjoint_left.mp clear in_ray in_base)

end SixVertexUnfolding
