import SixVertexUnfolding.Definitions
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality

/-! Strict angular bounds for rays in an open hemisphere, using Mathlib's angle triangle inequality. -/

namespace SixVertexUnfolding

open InnerProductGeometry
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A nonzero nonnegative combination of two positive-height rays still has positive height. -/
theorem positive_height_in_pair_cone (height : E →ₗ[ℝ] ℝ) (a b x : E)
    (ha : 0 < height a) (hb : 0 < height b) (nonzero : x ≠ 0)
    (member : x ∈ Submodule.span ℝ≥0 {a, b}) : 0 < height x := by
  obtain ⟨s, t, combination⟩ := Submodule.mem_span_pair.mp member
  have expression : (s : ℝ) • a + (t : ℝ) • b = x := by simpa only [NNReal.smul_def] using combination
  have balance := congrArg height expression
  simp only [map_add, map_smul, smul_eq_mul] at balance
  have some_positive : 0 < (s : ℝ) ∨ 0 < (t : ℝ) := by
    by_contra none
    push Not at none
    have sz : (s : ℝ) = 0 := le_antisymm none.1 s.property
    have tz : (t : ℝ) = 0 := le_antisymm none.2 t.property
    simp only [sz, tz, zero_smul, add_zero] at expression
    exact nonzero expression.symm
  rcases some_positive with positive | positive
  · nlinarith [mul_pos positive ha, mul_nonneg t.property hb.le]
  · nlinarith [mul_pos positive hb, mul_nonneg s.property ha.le]

/-- Two positive-height rays cannot point in opposite directions. -/
theorem angle_lt_pi_of_positive_height (height : E →ₗ[ℝ] ℝ) (a b : E)
    (ha : 0 < height a) (hb : 0 < height b) : angle a b < Real.pi := by
  apply (angle_le_pi a b).lt_of_ne
  intro straight
  obtain ⟨_, r, negative, expression⟩ := angle_eq_pi_iff.mp straight
  have balance := congrArg height expression
  simp only [map_smul, smul_eq_mul] at balance
  have opposite := mul_neg_of_neg_of_pos negative ha
  linarith

/-- Going through a nonpositive-height ray makes the angle triangle inequality strict. -/
theorem angle_triangle_strict_of_height (height : E →ₗ[ℝ] ℝ) (a x b : E)
    (ha : 0 < height a) (hb : 0 < height b) (hx : height x ≤ 0) (nonzero : x ≠ 0) :
    angle a b < angle a x + angle x b := by
  apply (angle_le_angle_add_angle a x b).lt_of_ne
  intro equality
  rcases (angle_eq_angle_add_angle_iff nonzero).mp equality with straight | inside
  · exact (angle_lt_pi_of_positive_height height a b ha hb).ne straight
  · exact (not_lt_of_ge hx) (positive_height_in_pair_cone height a b x ha hb nonzero inside)

/-- Four cyclic rays with crossing cone diagonals have angular perimeter strictly below two pi.
The diagonal coefficients may vanish, so a flat subdivision corner is permitted. -/
theorem spherical_quadrilateral_perimeter_lt (height : E →ₗ[ℝ] ℝ) (a b c d : E)
    (ha : 0 < height a) (hb : 0 < height b) (hc : 0 < height c) (hd : 0 < height d)
    (α β γ δ : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ)
    (diagonals : α • a + γ • c = β • b + δ • d)
    (nonzero : α • a - β • b ≠ 0) :
    angle a b + angle b c + angle c d + angle d a < 2 * Real.pi := by
  let e := α • a - β • b
  have e_nonzero : e ≠ 0 := nonzero
  have first_cone : e ∈ Submodule.span ℝ≥0 {a, -b} := by
    apply Submodule.mem_span_pair.mpr
    refine ⟨⟨α, hα⟩, ⟨β, hβ⟩, ?_⟩
    change α • a + β • (-b) = e
    dsimp [e]
    module
  have second_cone : e ∈ Submodule.span ℝ≥0 {d, -c} := by
    apply Submodule.mem_span_pair.mpr
    refine ⟨⟨δ, hδ⟩, ⟨γ, hγ⟩, ?_⟩
    change δ • d + γ • (-c) = e
    dsimp [e]
    linear_combination (norm := module) -diagonals
  have first : angle a (-b) = angle a e + angle e (-b) :=
    (angle_eq_angle_add_angle_iff e_nonzero).mpr (Or.inr first_cone)
  have second : angle d (-c) = angle d e + angle e (-c) :=
    (angle_eq_angle_add_angle_iff e_nonzero).mpr (Or.inr second_cone)
  simp only [angle_neg_right] at first second
  rw [angle_comm a e] at first
  rw [angle_comm d e, angle_comm d c] at second
  have first_edge : angle a b = angle e b - angle e a := by linarith
  have third_edge : angle c d = angle e c - angle e d := by linarith
  rw [first_edge, third_edge]
  by_cases nonpositive : height e ≤ 0
  · have short := angle_triangle_strict_of_height height d e a hd ha nonpositive e_nonzero
    have long := angle_le_angle_add_angle b (-e) c
    rw [angle_comm d e] at short
    simp only [angle_neg_right, angle_neg_left] at long
    rw [angle_comm b e] at long
    linarith
  · have negative : height (-e) ≤ 0 := by rw [map_neg]; linarith
    have short := angle_triangle_strict_of_height height b (-e) c hb hc negative (neg_ne_zero.mpr e_nonzero)
    have long := angle_le_angle_add_angle d e a
    simp only [angle_neg_right, angle_neg_left] at short
    rw [angle_comm b e] at short
    rw [angle_comm d e] at long
    linarith

end SixVertexUnfolding
