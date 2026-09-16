import SixVertexUnfolding.Definitions

/-! Concrete barycentric weights for a triangle and for points away from its edges. -/

namespace SixVertexUnfolding

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A point in a triangle is a convex combination of its three named vertices. -/
theorem triangle_weights (S U V q : E) (member : q ∈ convexHull ℝ ({S, U, V} : Set E)) :
    ∃ s u v : ℝ, 0 ≤ s ∧ 0 ≤ u ∧ 0 ≤ v ∧ s + u + v = 1 ∧ s • S + u • U + v • V = q := by
  rw [convexHull_insert (Set.insert_nonempty U {V}), convexHull_pair] at member
  obtain ⟨x, hx, y, hy, on_segment⟩ := mem_convexJoin.mp member
  have same : x = S := hx
  subst x
  obtain ⟨s, t, hs, ht, total, combination⟩ := on_segment
  obtain ⟨u, v, hu, hv, pair_total, pair_combination⟩ := hy
  refine ⟨s, t * u, t * v, hs, mul_nonneg ht hu, mul_nonneg ht hv, ?_, ?_⟩
  · nlinarith
  · rw [← combination, ← pair_combination]
    module

/-- Avoiding all three edges makes all three triangle weights strictly positive. -/
theorem triangle_positive_weights (S U V q : E)
    (member : q ∈ convexHull ℝ ({S, U, V} : Set E))
    (not_SU : q ∉ segment ℝ S U) (not_SV : q ∉ segment ℝ S V) (not_UV : q ∉ segment ℝ U V) :
    ∃ s u v : ℝ, 0 < s ∧ 0 < u ∧ 0 < v ∧ s + u + v = 1 ∧ s • S + u • U + v • V = q := by
  obtain ⟨s, u, v, hs, hu, hv, total, combination⟩ := triangle_weights S U V q member
  have s_pos : 0 < s := by
    apply lt_of_le_of_ne hs
    intro zero
    have s_zero : s = 0 := zero.symm
    rw [s_zero, zero_smul, zero_add] at combination
    exact not_UV ⟨u, v, hu, hv, by linarith, combination⟩
  have u_pos : 0 < u := by
    apply lt_of_le_of_ne hu
    intro zero
    have u_zero : u = 0 := zero.symm
    rw [u_zero, zero_smul, add_zero] at combination
    exact not_SV ⟨s, v, hs, hv, by linarith, combination⟩
  have v_pos : 0 < v := by
    apply lt_of_le_of_ne hv
    intro zero
    have v_zero : v = 0 := zero.symm
    rw [v_zero, zero_smul, add_zero] at combination
    exact not_SU ⟨s, u, hs, hu, by linarith, combination⟩
  exact ⟨s, u, v, s_pos, u_pos, v_pos, total, combination⟩

end SixVertexUnfolding
