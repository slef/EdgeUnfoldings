import SixVertexUnfolding.Geometry.FiniteSelectionContinuity
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Linarith

/-! A local distance bound from every center extends along a real interval.
This uses continuous induction and does not require differentiability. -/

namespace SixVertexUnfolding

open Set Filter Topology
open scoped NNReal

/-- Bounds from nearby centers add up to the same bound between the endpoints. -/
theorem interval_distance_of_center_bounds {Y : Type*} [MetricSpace Y]
    (f : ℝ → Y) (a b K : ℝ) (ordered : a ≤ b)
    (continuous_f : ContinuousOn f (Icc a b))
    (local_bound : ∀ x ∈ Icc a b, ∀ᶠ y in 𝓝[Icc a b] x,
      dist (f y) (f x) ≤ K * dist y x) :
    dist (f a) (f b) ≤ K * (b - a) := by
  let good : Set ℝ := {t | dist (f a) (f t) ≤ K * (t - a)}
  have closed : IsClosed (good ∩ Icc a b) := by
    rw [inter_comm]
    exact isClosed_Icc.isClosed_le
      ((continuous_const.dist continuous_id).comp_continuousOn continuous_f)
      (continuous_const.mul (continuous_id.sub continuous_const)).continuousOn
  have start : a ∈ good := by simp [good]
  have all_good := closed.Icc_subset_of_forall_mem_nhdsWithin start (fun x hx => ?_)
  · exact all_good ⟨ordered, le_rfl⟩
  · have near := (local_bound x ⟨hx.2.1, hx.2.2.le⟩).filter_mono
      (nhdsWithin_le_of_mem (Icc_mem_nhdsGT_of_mem hx.2))
    filter_upwards [near, self_mem_nhdsWithin] with y hy xy
    change x < y at xy
    change dist (f a) (f y) ≤ K * (y - a)
    have at_x : dist (f a) (f x) ≤ K * (x - a) := hx.1
    rw [dist_comm (f y) (f x), Real.dist_eq, abs_of_pos (sub_pos.mpr xy)] at hy
    calc
      dist (f a) (f y) ≤ dist (f a) (f x) + dist (f x) (f y) := dist_triangle _ _ _
      _ ≤ K * (x - a) + K * (y - x) := add_le_add at_x hy
      _ = K * (y - a) := by ring

/-- A continuous finite selection of Lipschitz pieces satisfies the endpoint bound. -/
theorem interval_distance_of_finite_pieces {Y ι : Type*} [MetricSpace Y] [Finite ι]
    (f : ℝ → Y) (g : ι → ℝ → Y) (a b : ℝ) (K : ℝ≥0) (ordered : a ≤ b)
    (continuous_f : ContinuousOn f (Icc a b))
    (pieces : ∀ i, LipschitzOnWith K (g i) (Icc a b))
    (selected : ∀ x ∈ Icc a b, ∃ i, f x = g i x) :
    dist (f a) (f b) ≤ K * (b - a) :=
  interval_distance_of_center_bounds f a b K ordered continuous_f
    (finite_selection_center_bound (Icc a b) f g K continuous_f pieces selected)

end SixVertexUnfolding
