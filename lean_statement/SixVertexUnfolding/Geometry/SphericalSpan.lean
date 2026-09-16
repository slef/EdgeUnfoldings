import SixVertexUnfolding.Geometry.SphericalAngles

/-! Equality in the angle triangle inequality forces its intermediate ray into the endpoint plane. -/

namespace SixVertexUnfolding

open InnerProductGeometry
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A point of a segment is a nonnegative combination of its endpoints. -/
theorem mem_pair_cone_of_segment (a b x : E) (member : x ∈ segment ℝ a b) :
    x ∈ Submodule.span ℝ≥0 {a, b} := by
  obtain ⟨s, t, hs, ht, _, combination⟩ := member
  exact Submodule.mem_span_pair.mpr ⟨⟨s, hs⟩, ⟨t, ht⟩, by simpa only [NNReal.smul_def] using combination⟩

/-- A nonzero point between two rays divides their angle additively. -/
theorem angle_add_of_segment (a b x : E) (nonzero : x ≠ 0) (member : x ∈ segment ℝ a b) :
    angle a b = angle a x + angle x b :=
  (angle_eq_angle_add_angle_iff nonzero).mpr (Or.inr (mem_pair_cone_of_segment a b x member))

/-- A nonnegative combination remains in every real subspace containing its generators. -/
theorem pair_cone_mem_subspace (S : Submodule ℝ E) (a b x : E) (ha : a ∈ S) (hb : b ∈ S)
    (member : x ∈ Submodule.span ℝ≥0 {a, b}) : x ∈ S := by
  obtain ⟨s, t, combination⟩ := Submodule.mem_span_pair.mp member
  have expression : (s : ℝ) • a + (t : ℝ) • b = x := by simpa only [NNReal.smul_def] using combination
  rw [← expression]
  exact S.add_mem (S.smul_mem _ ha) (S.smul_mem _ hb)

/-- For positive-height endpoints, an additive intermediate ray lies in their real plane. -/
theorem angle_add_mem_subspace (height : E →ₗ[ℝ] ℝ) (S : Submodule ℝ E) (a x b : E)
    (ha : 0 < height a) (hb : 0 < height b) (nonzero : x ≠ 0)
    (aS : a ∈ S) (bS : b ∈ S) (equality : angle a b = angle a x + angle x b) : x ∈ S := by
  rcases (angle_eq_angle_add_angle_iff nonzero).mp equality with straight | combination
  · exact ((angle_lt_pi_of_positive_height height a b ha hb).ne straight).elim
  · exact pair_cone_mem_subspace S a b x aS bS combination

end SixVertexUnfolding
