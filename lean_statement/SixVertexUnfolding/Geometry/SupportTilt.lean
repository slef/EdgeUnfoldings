import SixVertexUnfolding.Geometry.AffineDimension

/-!
Two ingredients for enlarging a supporting contact set: a spare orthogonal
direction in three-space, and the first new contact among finitely many vertices.
-/

namespace SixVertexUnfolding

/-- A subspace of dimension at most one leaves a direction orthogonal to it and to a given normal. -/
theorem exists_tilt_direction (D : Submodule ℝ Space) (n : Space)
    (dimension : Module.finrank ℝ D ≤ 1) (normal_nonzero : n ≠ 0) :
    ∃ q : Space, q ≠ 0 ∧ q ∈ Dᗮ ∧ inner ℝ n q = 0 := by
  let S := D ⊔ Submodule.span ℝ {n}
  have dimension_sum := D.finrank_sup_add_finrank_inf_eq (Submodule.span ℝ {n})
  rw [finrank_span_singleton normal_nonzero] at dimension_sum
  have orthogonal_sum := S.finrank_add_finrank_orthogonal
  have ambient : Module.finrank ℝ Space = 3 := by simp [Space]
  rw [ambient] at orthogonal_sum
  have nontrivial_orthogonal : Sᗮ ≠ ⊥ := by
    intro zero
    rw [zero] at orthogonal_sum
    simp only [finrank_bot, add_zero] at orthogonal_sum
    change Module.finrank ℝ S + Module.finrank ℝ (D ⊓ Submodule.span ℝ {n} : Submodule ℝ Space) =
      Module.finrank ℝ D + 1 at dimension_sum
    omega
  obtain ⟨q, hq, nonzero⟩ := Submodule.exists_mem_ne_zero_of_ne_bot nontrivial_orthogonal
  refine ⟨q, nonzero, ?_, ?_⟩
  · apply (D.mem_orthogonal q).mpr
    intro d hd
    exact S.inner_right_of_mem_orthogonal (show d ∈ S from Submodule.mem_sup_left hd) hq
  · exact S.inner_right_of_mem_orthogonal
      (show n ∈ S from Submodule.mem_sup_right (Submodule.mem_span_singleton_self n)) hq

/-- Moving a supporting plane until its first new contact preserves all old contacts. -/
theorem finite_support_tilt (vertices : Finset Space) (f g : Space → ℝ)
    (supported : ∀ v ∈ vertices, f v ≤ 0)
    (fixed_contacts : ∀ v ∈ vertices, f v = 0 → g v = 0)
    (forward : ∃ v ∈ vertices, 0 < g v) :
    ∃ t : ℝ, 0 < t ∧
      (∀ v ∈ vertices, f v + t * g v ≤ 0) ∧
      ∃ b ∈ vertices, f b < 0 ∧ f b + t * g b = 0 := by
  classical
  let forward_vertices := vertices.filter (fun v => 0 < g v)
  have forward_nonempty : forward_vertices.Nonempty := by
    obtain ⟨v, hv, positive⟩ := forward
    exact ⟨v, Finset.mem_filter.mpr ⟨hv, positive⟩⟩
  obtain ⟨b, hb, first⟩ := forward_vertices.exists_min_image
    (fun v => -f v / g v) forward_nonempty
  have b_in := (Finset.mem_filter.mp hb).1
  have b_forward := (Finset.mem_filter.mp hb).2
  have b_strict : f b < 0 := by
    have upper := supported b b_in
    have not_zero : f b ≠ 0 := by
      intro zero
      have fixed := fixed_contacts b b_in zero
      linarith
    exact lt_of_le_of_ne upper not_zero
  let t := -f b / g b
  have t_pos : 0 < t := div_pos (neg_pos.mpr b_strict) b_forward
  refine ⟨t, t_pos, ?_, b, b_in, b_strict, ?_⟩
  · intro v hv
    by_cases advancing : 0 < g v
    · have earliest : t ≤ -f v / g v :=
        first v (Finset.mem_filter.mpr ⟨hv, advancing⟩)
      have bound := (le_div_iff₀ advancing).mp earliest
      linarith
    · have backward : t * g v ≤ 0 := mul_nonpos_of_nonneg_of_nonpos t_pos.le (by linarith)
      linarith [supported v hv]
  · dsimp [t]
    rw [div_mul_cancel₀ _ (ne_of_gt b_forward)]
    ring

end SixVertexUnfolding
