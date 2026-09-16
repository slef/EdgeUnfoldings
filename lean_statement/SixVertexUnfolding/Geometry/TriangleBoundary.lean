import SixVertexUnfolding.Definitions

/-! The boundary of a nondegenerate planar triangle consists of its three whole edges. -/

namespace SixVertexUnfolding

/-- Barycentric coordinates put every boundary point on one of the three edge segments. -/
theorem triangle_frontier_subset_edges (a b c : Plane)
    (noncollinear : ¬ Collinear ℝ ({a, b, c} : Set Plane)) :
    frontier (convexHull ℝ ({a, b, c} : Set Plane)) ⊆
      segment ℝ a b ∪ (segment ℝ a c ∪ segment ℝ b c) := by
  have independent : AffineIndependent ℝ ![a, b, c] :=
    affineIndependent_iff_not_collinear_set.mpr noncollinear
  let basis : AffineBasis (Fin 3) ℝ Plane := {
    toFun := ![a, b, c]
    ind' := independent
    tot' := independent.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp [Plane])
  }
  have range_eq : Set.range basis = ({a, b, c} : Set Plane) := by
    change Set.range ![a, b, c] = _
    ext x
    simp [Matrix.range_cons, Matrix.range_empty]
    tauto
  rw [← range_eq]
  have closed := (Set.finite_range basis).isClosed_convexHull ℝ
  intro x boundary
  rw [closed.frontier_eq] at boundary
  have nonnegative : ∀ i, 0 ≤ basis.coord i x := by
    simpa only [basis.convexHull_eq_nonneg_coord, Set.mem_setOf_eq] using boundary.1
  have not_positive : ¬ ∀ i, 0 < basis.coord i x := by
    intro positive
    apply boundary.2
    simpa only [basis.interior_convexHull, Set.mem_setOf_eq] using positive
  push Not at not_positive
  obtain ⟨i, nonpositive⟩ := not_positive
  have zero : basis.coord i x = 0 := le_antisymm nonpositive (nonnegative i)
  have total := basis.sum_coord_apply_eq_one x
  have combination := basis.linear_combination_coord_eq_self x
  simp only [Fin.sum_univ_three] at total combination
  change basis.coord 0 x • a + basis.coord 1 x • b + basis.coord 2 x • c = x at combination
  fin_cases i
  · change basis.coord 0 x = 0 at zero
    rw [zero, zero_smul, zero_add] at combination
    exact Or.inr (Or.inr ⟨basis.coord 1 x, basis.coord 2 x, nonnegative 1, nonnegative 2,
      by linarith, combination⟩)
  · change basis.coord 1 x = 0 at zero
    rw [zero, zero_smul, add_zero] at combination
    exact Or.inr (Or.inl ⟨basis.coord 0 x, basis.coord 2 x, nonnegative 0, nonnegative 2,
      by linarith, combination⟩)
  · change basis.coord 2 x = 0 at zero
    rw [zero, zero_smul, add_zero] at combination
    exact Or.inl ⟨basis.coord 0 x, basis.coord 1 x, nonnegative 0, nonnegative 1,
      by linarith, combination⟩

end SixVertexUnfolding
