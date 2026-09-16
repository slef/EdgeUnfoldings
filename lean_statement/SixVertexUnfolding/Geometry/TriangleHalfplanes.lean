import SixVertexUnfolding.Geometry.TwoRayCones

/-! Three oriented edge half-planes give actual membership in a closed planar triangle. -/

namespace SixVertexUnfolding

theorem triangle_mem_of_weights (a b c x : Plane) (s t u : ℝ)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hu : 0 ≤ u) (total : s + t + u = 1)
    (expression : s • a + t • b + u • c = x) : x ∈ convexHull ℝ ({a, b, c} : Set Plane) := by
  let weight : Fin 3 → ℝ := ![s, t, u]
  let point : Fin 3 → Plane := ![a, b, c]
  have member := (convex_convexHull ℝ ({a, b, c} : Set Plane)).sum_mem
    (t := Finset.univ) (w := weight) (z := point)
    (by intro i _; fin_cases i; exacts [hs, ht, hu])
    (by simpa [weight, Fin.sum_univ_three] using total)
    (by intro i _; apply subset_convexHull ℝ _; fin_cases i <;> simp [point])
  have combination : s • a + t • b + u • c ∈ convexHull ℝ ({a, b, c} : Set Plane) := by
    simpa only [Fin.sum_univ_three, weight, point, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] using member
  rwa [expression] at combination

/-- This formulation includes all three edges and vertices; no general-position assumption is used. -/
theorem triangle_mem_of_three_halfplanes (b c x : Plane) (area_pos : 0 < det b c)
    (base : 0 ≤ det b x) (left : 0 ≤ det x c) (right : 0 ≤ det (c - b) (x - b)) :
    x ∈ convexHull ℝ ({0, b, c} : Set Plane) := by
  obtain ⟨t, u, ht, hu, expression⟩ := (mem_twoRayCone_iff_dets b c x area_pos).mpr ⟨base, left⟩
  have area : det (c - b) (x - b) = (1 - t - u) * det b c := by
    rw [expression]
    simp only [det, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have remaining : 0 ≤ 1 - t - u := by
    rw [area] at right
    by_contra negative
    have impossible := mul_neg_of_neg_of_pos (lt_of_not_ge negative) area_pos
    linarith
  apply triangle_mem_of_weights 0 b c x (1 - t - u) t u remaining ht hu (by ring)
  simpa only [smul_zero, zero_add] using expression.symm

end SixVertexUnfolding
