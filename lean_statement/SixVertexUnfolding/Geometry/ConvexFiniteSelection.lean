import SixVertexUnfolding.Geometry.IntervalCenterBound
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Convex.Basic

/-! A continuous map assembled from finitely many nonexpanding pieces
is nonexpanding on a convex set. The pieces may change along a segment. -/

namespace SixVertexUnfolding

open Set
open scoped NNReal

/-- A continuous finite selection on a convex set keeps the common Lipschitz bound. -/
theorem convex_finite_selection_lipschitz {E Y ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MetricSpace Y] [Finite ι]
    (s : Set E) (convex_s : Convex ℝ s) (f : E → Y) (g : ι → E → Y) (K : ℝ≥0)
    (continuous_f : ContinuousOn f s) (pieces : ∀ i, LipschitzOnWith K (g i) s)
    (selected : ∀ x ∈ s, ∃ i, f x = g i x) : LipschitzOnWith K f s := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  let line : ℝ → E := AffineMap.lineMap x y
  let bound : ℝ≥0 := K * nndist x y
  have inside : MapsTo line (Icc 0 1) s := convex_s.mapsTo_lineMap hx hy
  have continuous_line : Continuous line := (lipschitzWith_lineMap x y).continuous
  have piece_bound (i : ι) : LipschitzOnWith bound (fun t => g i (line t)) (Icc 0 1) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro t ht u hu
    calc
      dist (g i (line t)) (g i (line u)) ≤ K * dist (line t) (line u) :=
        (pieces i).dist_le_mul _ (inside ht) _ (inside hu)
      _ = bound * dist t u := by
        rw [show dist (line t) (line u) = dist t u * dist x y from
          dist_lineMap_lineMap x y t u]
        simp only [bound, NNReal.coe_mul, coe_nndist]
        ring
  have endpoint := interval_distance_of_finite_pieces (fun t => f (line t))
    (fun i t => g i (line t)) 0 1 bound zero_le_one
    (continuous_f.comp continuous_line.continuousOn inside) piece_bound
    (fun t ht => selected _ (inside ht))
  simpa only [line, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one,
    sub_zero, mul_one, bound, NNReal.coe_mul, coe_nndist] using endpoint

/-- The same result for a map whose domain is the convex set itself. -/
theorem convex_subtype_finite_selection_lipschitz {E Y ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MetricSpace Y] [Finite ι]
    (s : Set E) (convex_s : Convex ℝ s) (f : s → Y) (g : ι → E → Y) (K : ℝ≥0)
    (continuous_f : Continuous f) (pieces : ∀ i, LipschitzOnWith K (g i) s)
    (selected : ∀ x : s, ∃ i, f x = g i x) : LipschitzWith K f := by
  classical
  apply LipschitzWith.of_dist_le_mul
  intro x y
  let extension : E → Y := Function.extend Subtype.val f (fun _ => f x)
  have agrees (z : s) : extension z = f z := Subtype.val_injective.extend_apply _ _ z
  have restricted : s.restrict extension = f := funext agrees
  have continuous_extension : ContinuousOn extension s :=
    continuousOn_iff_continuous_restrict.mpr (restricted.symm ▸ continuous_f)
  have bound := convex_finite_selection_lipschitz s convex_s extension g K continuous_extension pieces (by
    intro z hz
    obtain ⟨i, hi⟩ := selected ⟨z, hz⟩
    exact ⟨i, (agrees ⟨z, hz⟩).trans hi⟩)
  simpa only [agrees] using bound.dist_le_mul x x.property y y.property

end SixVertexUnfolding
