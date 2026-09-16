import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Order.OrderClosed

/-! A continuous choice among finitely many continuous maps can only
switch, near a point, to a map that has the same value at that point. -/

namespace SixVertexUnfolding

open Set Filter Topology
open scoped NNReal

/-- Near a given point, every selected piece agrees with the selection at that point. -/
theorem finite_selection_nearby_pieces {X Y ι : Type*} [TopologicalSpace X]
    [MetricSpace Y] [Finite ι] (s : Set X) (f : X → Y) (g : ι → X → Y)
    (continuous_f : ContinuousOn f s) (continuous_g : ∀ i, ContinuousOn (g i) s)
    (x : X) (hx : x ∈ s) :
    ∀ᶠ y in 𝓝[s] x, ∀ i, f y = g i y → f x = g i x := by
  classical
  apply Filter.eventually_all.mpr
  intro i
  by_cases same : f x = g i x
  · exact Filter.Eventually.of_forall (fun _ _ => same)
  · have limit : Tendsto (fun y => dist (f y) (g i y)) (𝓝[s] x)
        (𝓝 (dist (f x) (g i x))) :=
      continuous_dist.continuousAt.tendsto.comp
        ((continuous_f x hx).prodMk_nhds (continuous_g i x hx))
    have positive : ∀ᶠ y in 𝓝[s] x, 0 < dist (f y) (g i y) :=
      limit (isOpen_Ioi.mem_nhds (dist_pos.mpr same))
    filter_upwards [positive] with y hy equal
    rw [equal, dist_self] at hy
    exact (lt_irrefl 0 hy).elim

/-- Finitely many nonexpanding pieces give a nonexpanding bound from each nearby center. -/
theorem finite_selection_center_bound {X Y ι : Type*} [MetricSpace X] [MetricSpace Y]
    [Finite ι] (s : Set X) (f : X → Y) (g : ι → X → Y) (K : ℝ≥0)
    (continuous_f : ContinuousOn f s) (pieces : ∀ i, LipschitzOnWith K (g i) s)
    (selected : ∀ x ∈ s, ∃ i, f x = g i x) (x : X) (hx : x ∈ s) :
    ∀ᶠ y in 𝓝[s] x, dist (f y) (f x) ≤ K * dist y x := by
  have active := finite_selection_nearby_pieces s f g continuous_f
    (fun i => (pieces i).continuousOn) x hx
  filter_upwards [active, self_mem_nhdsWithin] with y hy ys
  obtain ⟨i, at_y⟩ := selected y ys
  rw [at_y, hy i at_y]
  exact (pieces i).dist_le_mul y ys x hx

end SixVertexUnfolding
