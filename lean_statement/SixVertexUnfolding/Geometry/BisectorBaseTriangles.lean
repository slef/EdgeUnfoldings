import SixVertexUnfolding.Definitions
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-! Two distinct sites equidistant from both endpoints of a nontrivial
base give nondegenerate triangles on that base. -/

namespace SixVertexUnfolding

open Set

/-- Squared distance along an affine line is determined by the two endpoint distances. -/
theorem squared_distance_lineMap {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p u v : E) (t : ℝ) :
    dist p (AffineMap.lineMap u v t) ^ 2 =
      (1 - t) * dist p u ^ 2 + t * dist p v ^ 2 - t * (1 - t) * dist u v ^ 2 := by
  simp only [AffineMap.lineMap_apply_module, dist_eq_norm, ← real_inner_self_eq_norm_sq,
    inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right]
  simp only [real_inner_comm]
  ring

/-- A site on the base line is determined uniquely by its distances to the two base endpoints. -/
theorem equidistant_base_sites_eq_of_on_line {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p q u v : E) (left : dist p u = dist q u) (right : dist p v = dist q v)
    (on_line : p ∈ affineSpan ℝ ({u, v} : Set E)) : p = q := by
  obtain ⟨t, at_t⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp on_line
  have first := squared_distance_lineMap p u v t
  have second := squared_distance_lineMap q u v t
  rw [at_t, dist_self, left, right] at first
  rw [at_t] at second
  have zero : dist q p = 0 := by nlinarith [dist_nonneg (x := q) (y := p)]
  exact (dist_eq_zero.mp zero).symm

/-- Distinct equidistant sites cannot form a degenerate triangle with a nontrivial base. -/
theorem bisector_base_noncollinear {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p q u v : E) (sites_different : p ≠ q) (base_different : u ≠ v)
    (left : dist p u = dist q u) (right : dist p v = dist q v) :
    ¬ Collinear ℝ ({p, u, v} : Set E) := by
  intro collinear
  apply sites_different
  exact equidistant_base_sites_eq_of_on_line p q u v left right
    (collinear.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) base_different)

end SixVertexUnfolding
