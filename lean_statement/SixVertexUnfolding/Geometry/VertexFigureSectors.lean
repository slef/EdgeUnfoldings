import SixVertexUnfolding.Geometry.VertexFigure
import SixVertexUnfolding.Geometry.TriangleWeights

/-! Radial projection takes a punctured triangular vertex sector to the
corresponding side of the actual transverse vertex figure. -/

namespace SixVertexUnfolding.ConvexPolyhedron.VertexFigure

open Set

variable {P : ConvexPolyhedron} {pole : P.Vertex} (figure : P.VertexFigure pole)

/-- The gap is affine on a triangle based at the supporting vertex. -/
theorem gap_combination (a b : Space) (u v w : ℝ) (total : u + v + w = 1) :
    figure.gap (u • (pole : Space) + v • a + w • b) = v * figure.gap a + w * figure.gap b := by
  simp only [gap, inner_add_right, inner_smul_right]
  nlinarith [congrArg (fun t : ℝ => t * inner ℝ figure.normal (pole : Space)) total]

/-- Every nonvertex point of an incident triangle has positive transverse height. -/
theorem sector_gap_positive (a b : Space) (a_pos : 0 < figure.gap a)
    (b_pos : 0 < figure.gap b) (x : Space)
    (member : x ∈ convexHull ℝ ({(pole : Space), a, b} : Set Space))
    (nonpole : x ≠ pole) : 0 < figure.gap x := by
  obtain ⟨u, v, w, hu, hv, hw, total, combination⟩ := triangle_weights _ _ _ _ member
  have positive : 0 < v ∨ 0 < w := by
    by_contra neither
    push Not at neither
    have vz : v = 0 := le_antisymm neither.1 hv
    have wz : w = 0 := le_antisymm neither.2 hw
    have uz : u = 1 := by linarith
    exact nonpole (by simpa only [vz, wz, uz, zero_smul, one_smul, add_zero] using combination.symm)
  rw [← combination, figure.gap_combination a b u v w total]
  rcases positive with vp | wp
  · exact add_pos_of_pos_of_nonneg (mul_pos vp a_pos) (mul_nonneg hw b_pos.le)
  · exact add_pos_of_nonneg_of_pos (mul_nonneg hv a_pos.le) (mul_pos wp b_pos)

/-- Normalizing by height maps the sector onto its transverse side. -/
theorem sector_direction_in_side (a b : Space) (a_pos : 0 < figure.gap a)
    (b_pos : 0 < figure.gap b) (x : Space)
    (member : x ∈ convexHull ℝ ({(pole : Space), a, b} : Set Space))
    (nonpole : x ≠ pole) : figure.direction x ∈ segment ℝ (figure.direction a) (figure.direction b) := by
  have xp := figure.sector_gap_positive a b a_pos b_pos x member nonpole
  obtain ⟨u, v, w, hu, hv, hw, total, combination⟩ := triangle_weights _ _ _ _ member
  have gap_x : figure.gap x = v * figure.gap a + w * figure.gap b := by
    rw [← combination, figure.gap_combination a b u v w total]
  refine ⟨v * figure.gap a / figure.gap x, w * figure.gap b / figure.gap x,
    div_nonneg (mul_nonneg hv a_pos.le) xp.le,
    div_nonneg (mul_nonneg hw b_pos.le) xp.le, ?_, ?_⟩
  · rw [← add_div, ← gap_x, div_self xp.ne']
  · simp only [direction, smul_smul]
    have first : v * figure.gap a / figure.gap x * (figure.gap a)⁻¹ = v / figure.gap x := by
      field_simp
    have second : w * figure.gap b / figure.gap x * (figure.gap b)⁻¹ = w / figure.gap x := by
      field_simp
    rw [first, second, ← combination]
    have shift : u • (pole : Space) + v • a + w • b - pole =
        v • (a - pole) + w • (b - pole) := by
      rw [show u = 1 - v - w by linarith]
      module
    rw [shift, smul_add, smul_smul, smul_smul]
    congr 1 <;> congr 1 <;> ring

/-- Equal projected directions give a positive multiple of the same spatial ray. -/
theorem equal_direction_ray (a x : Space) (a_pos : 0 < figure.gap a)
    (x_pos : 0 < figure.gap x) (same : figure.direction x = figure.direction a) :
    ∃ t : ℝ, 0 < t ∧ x = t • (a - pole) + pole := by
  refine ⟨figure.gap x / figure.gap a, div_pos x_pos a_pos, ?_⟩
  have scaled := congrArg (fun z : Space => figure.gap x • z) same
  simp only [direction, smul_smul, mul_inv_cancel₀ x_pos.ne', one_smul] at scaled
  simpa only [div_eq_mul_inv, sub_eq_iff_eq_add] using scaled

end SixVertexUnfolding.ConvexPolyhedron.VertexFigure
