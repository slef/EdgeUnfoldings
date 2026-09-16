import SixVertexUnfolding.Geometry.SphericalAngles
import SixVertexUnfolding.Geometry.TriangleWeights
import Mathlib.Analysis.Convex.Radon

/-! Four cyclic vertex-figure directions, including a possible flat subdivision corner. -/

namespace SixVertexUnfolding

/-- A transverse convex four-corner fan, specified by its actual supporting sides. -/
structure FourRayFan where
  ray : Fin 4 → Space
  distinct : Function.Injective ray
  height : Space →ₗ[ℝ] ℝ
  level : ∀ i, height (ray i) = 1
  spans : Submodule.span ℝ (Set.range ray) = ⊤
  side : Fin 4 → Space →ₗ[ℝ] ℝ
  side_nonzero : ∀ i, side i ≠ 0
  side_left : ∀ i, side i (ray i) = 0
  side_right : ∀ i, side i (ray (i + 1)) = 0
  side_bound : ∀ i j, side i (ray j) ≤ 0

namespace FourRayFan

variable (fan : FourRayFan)

/-- Each supporting side has a strictly lower corner because the rays span three dimensions. -/
theorem side_has_negative (i : Fin 4) : ∃ j, fan.side i (fan.ray j) < 0 := by
  by_contra none
  push Not at none
  have vanishes : ∀ j, fan.side i (fan.ray j) = 0 :=
    fun j => le_antisymm (fan.side_bound i j) (none j)
  have kernel : (fan.side i).ker = ⊤ := by
    apply top_unique
    rw [← fan.spans]
    apply Submodule.span_le.mpr
    rintro x ⟨j, rfl⟩
    exact vanishes j
  exact fan.side_nonzero i (LinearMap.ker_eq_top.mp kernel)

/-- The common transverse height places all four ray endpoints in an affine plane. -/
theorem affinely_dependent : ¬ AffineIndependent ℝ fan.ray := by
  intro independent
  have full := independent.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp [Space])
  have constant : Set.EqOn fan.height.toAffineMap (AffineMap.const ℝ Space (1 : ℝ)) (Set.range fan.ray) := by
    rintro x ⟨i, rfl⟩
    exact fan.level i
  have at_zero := AffineMap.eqOn_affineSpan constant (show (0 : Space) ∈ affineSpan ℝ (Set.range fan.ray) by rw [full]; trivial)
  norm_num at at_zero

/-- Start the same cyclic fan at any of its four corners. -/
def rotate (i : Fin 4) : FourRayFan where
  ray := fun j => fan.ray (i + j)
  distinct := by
    intro j k same
    exact add_left_cancel (fan.distinct same)
  height := fan.height
  level := fun j => fan.level (i + j)
  spans := by
    have points : Set.range (fun j => fan.ray (i + j)) = Set.range fan.ray := by
      ext x
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨i + j, rfl⟩
      · rintro ⟨j, rfl⟩
        exact ⟨j - i, by simp⟩
    rw [points]
    exact fan.spans
  side := fun j => fan.side (i + j)
  side_nonzero := fun j => fan.side_nonzero (i + j)
  side_left := fun j => fan.side_left (i + j)
  side_right := fun j => by simpa only [add_assoc] using fan.side_right (i + j)
  side_bound := fun j k => fan.side_bound (i + j) (i + k)

/-- A corner in the hull of the other three can only be a flat corner between its two neighbors. -/
theorem corner_in_neighbors (member : fan.ray 0 ∈ convexHull ℝ ({fan.ray 1, fan.ray 2, fan.ray 3} : Set Space)) :
    fan.ray 0 ∈ segment ℝ (fan.ray 1) (fan.ray 3) := by
  obtain ⟨u, v, w, hu, hv, hw, total, combination⟩ := triangle_weights _ _ _ _ member
  have first := congrArg (fan.side 0) combination
  have last := congrArg (fan.side 3) combination
  simp only [map_add, map_smul, smul_eq_mul] at first last
  have s00 := fan.side_left 0
  have s01 : fan.side 0 (fan.ray 1) = 0 := fan.side_right 0
  have s33 := fan.side_left 3
  have s30 : fan.side 3 (fan.ray 0) = 0 := fan.side_right 3
  have v_zero : v = 0 := by
    by_contra nonzero
    have positive : 0 < v := lt_of_le_of_ne hv (Ne.symm nonzero)
    have s02 : fan.side 0 (fan.ray 2) = 0 := by
      nlinarith [fan.side_bound 0 2, mul_nonpos_of_nonneg_of_nonpos hw (fan.side_bound 0 3)]
    have s32 : fan.side 3 (fan.ray 2) = 0 := by
      nlinarith [fan.side_bound 3 2, mul_nonpos_of_nonneg_of_nonpos hu (fan.side_bound 3 1)]
    have s03 : fan.side 0 (fan.ray 3) < 0 := by
      obtain ⟨j, negative⟩ := fan.side_has_negative 0
      fin_cases j
      · exact (not_lt_of_ge s00.ge negative).elim
      · exact (not_lt_of_ge s01.ge negative).elim
      · exact (not_lt_of_ge s02.ge negative).elim
      · exact negative
    have s31 : fan.side 3 (fan.ray 1) < 0 := by
      obtain ⟨j, negative⟩ := fan.side_has_negative 3
      fin_cases j
      · exact (not_lt_of_ge s30.ge negative).elim
      · exact negative
      · exact (not_lt_of_ge s32.ge negative).elim
      · exact (not_lt_of_ge s33.ge negative).elim
    have u_zero : u = 0 := by nlinarith
    have w_zero : w = 0 := by nlinarith
    have v_one : v = 1 := by linarith
    have same : fan.ray 2 = fan.ray 0 := by simpa only [u_zero, w_zero, v_one, zero_smul, one_smul, zero_add, add_zero] using combination
    exact (by decide : (2 : Fin 4) ≠ 0) (fan.distinct same)
  refine ⟨u, w, hu, hw, by linarith, ?_⟩
  simpa only [v_zero, zero_smul, add_zero] using combination

end FourRayFan
end SixVertexUnfolding
