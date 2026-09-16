import SixVertexUnfolding.Definitions
import Mathlib.Topology.Order.OrderClosed

/-! Two rigid half-planes joined along their common line give a continuous
folding. Its Euclidean distances can only decrease. -/

namespace SixVertexUnfolding

open Set

/-- Internal data for folding the two sides of one planar line into space. -/
structure FoldedPlane where
  height : Plane →ᵃ[ℝ] ℝ
  first : Plane →ᵃ[ℝ] Space
  second : Plane →ᵃ[ℝ] Space
  first_rigid : ∀ x y, dist (first x) (first y) = dist x y
  second_rigid : ∀ x y, dist (second x) (second y) = dist x y
  joined : ∀ x, height x = 0 → first x = second x

namespace FoldedPlane

variable (fold : FoldedPlane)

/-- Fold positive and negative sides using their respective rigid placements. -/
noncomputable def map (x : Plane) : Space :=
  if 0 ≤ fold.height x then fold.first x else fold.second x

theorem map_of_nonnegative {x : Plane} (hx : 0 ≤ fold.height x) : fold.map x = fold.first x :=
  if_pos hx

theorem map_of_nonpositive {x : Plane} (hx : fold.height x ≤ 0) : fold.map x = fold.second x := by
  by_cases zero : fold.height x = 0
  · rw [map_of_nonnegative fold zero.ge, fold.joined x zero]
  · exact if_neg (not_le.mpr (lt_of_le_of_ne hx zero))

/-- The two rules glue continuously on their common line. -/
theorem continuous : Continuous fold.map := by
  apply Continuous.if_le fold.first.continuous_of_finiteDimensional
    fold.second.continuous_of_finiteDimensional continuous_const fold.height.continuous_of_finiteDimensional
  exact fun x hx => fold.joined x hx.symm

/-- A segment between opposite closed half-planes meets the folding line. -/
theorem segment_meets_crease (x y : Plane) (hx : 0 ≤ fold.height x) (hy : fold.height y ≤ 0) :
    ∃ z ∈ segment ℝ x y, fold.height z = 0 := by
  by_cases zero : fold.height x = 0
  · exact ⟨x, left_mem_segment ℝ x y, zero⟩
  have positive : 0 < fold.height x := lt_of_le_of_ne hx (Ne.symm zero)
  have denominator : 0 < fold.height x - fold.height y := by linarith
  let t := fold.height x / (fold.height x - fold.height y)
  have nonnegative : 0 ≤ t := div_nonneg hx denominator.le
  have at_most_one : t ≤ 1 := (div_le_one denominator).mpr (by linarith)
  refine ⟨AffineMap.lineMap x y t, ?_, ?_⟩
  · rw [segment_eq_image_lineMap]
    exact ⟨t, ⟨nonnegative, at_most_one⟩, rfl⟩
  · rw [AffineMap.apply_lineMap, AffineMap.lineMap_apply_module']
    dsimp [t]
    field_simp
    ring

/-- Folding a segment across its crease cannot increase endpoint distance. -/
theorem opposite_distance_le (x y : Plane) (hx : 0 ≤ fold.height x) (hy : fold.height y ≤ 0) :
    dist (fold.first x) (fold.second y) ≤ dist x y := by
  obtain ⟨z, between, zero⟩ := fold.segment_meets_crease x y hx hy
  calc
    dist (fold.first x) (fold.second y) ≤
        dist (fold.first x) (fold.first z) + dist (fold.first z) (fold.second y) := dist_triangle _ _ _
    _ = dist x z + dist z y := by rw [fold.first_rigid, fold.joined z zero, fold.second_rigid]
    _ = dist x y := dist_add_dist_eq_iff.mpr (mem_segment_iff_wbtw.mp between)

/-- A folded plane is 1-Lipschitz in the ambient Euclidean distances. -/
theorem lipschitz : LipschitzWith 1 fold.map := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul]
  by_cases hx : 0 ≤ fold.height x <;> by_cases hy : 0 ≤ fold.height y
  · rw [fold.map_of_nonnegative hx, fold.map_of_nonnegative hy, fold.first_rigid]
  · rw [fold.map_of_nonnegative hx, fold.map_of_nonpositive (le_of_not_ge hy)]
    exact fold.opposite_distance_le x y hx (le_of_not_ge hy)
  · rw [fold.map_of_nonpositive (le_of_not_ge hx), fold.map_of_nonnegative hy, dist_comm, dist_comm x y]
    exact fold.opposite_distance_le y x hy (le_of_not_ge hx)
  · rw [fold.map_of_nonpositive (le_of_not_ge hx), fold.map_of_nonpositive (le_of_not_ge hy), fold.second_rigid]

end FoldedPlane
end SixVertexUnfolding
