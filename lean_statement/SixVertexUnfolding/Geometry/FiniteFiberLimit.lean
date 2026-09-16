import SixVertexUnfolding.Geometry.FiniteClusterLimit
import Mathlib.Topology.Algebra.Order.Field

/-! Endpoint limits for continuous curves lying over a converging target,
when the limiting target has only finitely many possible lifts. -/

namespace SixVertexUnfolding

open Set Filter Topology

/-- Compactness and a finite limiting fiber force a continuous lift to converge. -/
theorem finite_fiber_right_limit {Y Z : Type*} [MetricSpace Y] [TopologicalSpace Z] [T2Space Z]
    (f : ℝ → Y) (continuous_f : ContinuousOn f (Ioo 0 1))
    (K : Set Y) (compactK : IsCompact K) (contained : ∀ t ∈ Ioo (0 : ℝ) 1, f t ∈ K)
    (h : Y → Z) (continuous_h : Continuous h) (z : Z)
    (limit : Tendsto (h ∘ f) (𝓝[>] (0 : ℝ)) (𝓝 z))
    (finite_fiber : (K ∩ h ⁻¹' {z}).Finite) :
    ∃ y ∈ K, h y = z ∧ Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 y) := by
  obtain ⟨y, hy, converges⟩ := finite_cluster_right_limit f continuous_f K compactK contained
    (K ∩ h ⁻¹' {z}) finite_fiber (fun q qK cluster_q =>
      ⟨qK, eq_of_nhds_neBot ((cluster_q.continuousAt_comp continuous_h.continuousAt).clusterPt.mono limit)⟩)
  exact ⟨y, hy.1, hy.2, converges⟩

/-- Reversing the unit interval approaches its right endpoint from the left. -/
theorem reverse_tendsto_right :
    Tendsto (fun t : ℝ => 1 - t) (𝓝[>] (0 : ℝ)) (𝓝[<] (1 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa using ((continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).sub continuous_id).continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  · filter_upwards [self_mem_nhdsWithin] with t ht
    change 1 - t < 1
    change 0 < t at ht
    linarith [ht]

/-- The same reversal takes a left approach at one to a right approach at zero. -/
theorem reverse_tendsto_left :
    Tendsto (fun t : ℝ => 1 - t) (𝓝[<] (1 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa using ((continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).sub continuous_id).continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[<] (1 : ℝ) ≤ 𝓝 1)
  · filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < 1 - t
    change t < 1 at ht
    linarith [ht]

/-- The corresponding finite-fiber limit at the right endpoint. -/
theorem finite_fiber_left_limit {Y Z : Type*} [MetricSpace Y] [TopologicalSpace Z] [T2Space Z]
    (f : ℝ → Y) (continuous_f : ContinuousOn f (Ioo 0 1))
    (K : Set Y) (compactK : IsCompact K) (contained : ∀ t ∈ Ioo (0 : ℝ) 1, f t ∈ K)
    (h : Y → Z) (continuous_h : Continuous h) (z : Z)
    (limit : Tendsto (h ∘ f) (𝓝[<] (1 : ℝ)) (𝓝 z))
    (finite_fiber : (K ∩ h ⁻¹' {z}).Finite) :
    ∃ y ∈ K, h y = z ∧ Tendsto f (𝓝[<] (1 : ℝ)) (𝓝 y) := by
  have reverse_mem (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : 1 - t ∈ Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [ht.1, ht.2]
  obtain ⟨y, yK, at_y, converges⟩ := finite_fiber_right_limit (fun t => f (1 - t))
    (continuous_f.comp (continuous_const.sub continuous_id).continuousOn reverse_mem)
    K compactK (fun t ht => contained _ (reverse_mem t ht)) h continuous_h z
    (limit.comp reverse_tendsto_right) finite_fiber
  refine ⟨y, yK, at_y, ?_⟩
  simpa only [Function.comp_def, sub_sub_cancel] using converges.comp reverse_tendsto_left

end SixVertexUnfolding
