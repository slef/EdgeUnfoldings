import SixVertexUnfolding.Geometry.FiniteFiberLimit
import Mathlib.Topology.Order.ExtendFrom
import Mathlib.Topology.UnitInterval

/-! A compact continuous family with finite fibers over the two endpoint
targets extends from the open unit interval to the closed one. -/

namespace SixVertexUnfolding

open Set Filter Topology

/-- Extend a continuously chosen lift to both endpoints, retaining its actual target. -/
theorem finite_fiber_interval_extension {Y Z : Type*} [MetricSpace Y] [TopologicalSpace Z] [T2Space Z]
    (f : C(Ioo (0 : ℝ) 1, Y)) (K : Set Y) (compactK : IsCompact K)
    (contained : ∀ t, f t ∈ K) (h : Y → Z) (continuous_h : Continuous h)
    (target : C(ℝ, Z)) (over_target : ∀ t, h (f t) = target t)
    (finite_left : (K ∩ h ⁻¹' {target 0}).Finite)
    (finite_right : (K ∩ h ⁻¹' {target 1}).Finite) :
    ∃ g : C(unitInterval, Y),
      (∀ t : Ioo (0 : ℝ) 1, g ⟨t, t.property.1.le, t.property.2.le⟩ = f t) ∧
      ∀ t, g t ∈ K ∧ h (g t) = target t := by
  classical
  let middle : Ioo (0 : ℝ) 1 := ⟨1 / 2, by norm_num⟩
  let real_f (t : ℝ) := if ht : t ∈ Ioo (0 : ℝ) 1 then f ⟨t, ht⟩ else f middle
  have real_eq (t : Ioo (0 : ℝ) 1) : real_f t = f t := by
    dsimp only [real_f]
    rw [dif_pos t.property]
  have continuous_real : ContinuousOn real_f (Ioo 0 1) := by
    apply continuousOn_iff_continuous_restrict.mpr
    convert f.continuous using 1
    exact funext real_eq
  have real_contained (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : real_f t ∈ K := by
    rw [real_eq ⟨t, ht⟩]
    exact contained _
  have real_target (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : h (real_f t) = target t := by
    rw [real_eq ⟨t, ht⟩]
    exact over_target _
  have left_limit : Tendsto (h ∘ real_f) (𝓝[>] (0 : ℝ)) (𝓝 (target 0)) := by
    apply (target.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with t ht
    exact (real_target t ht).symm
  have right_limit : Tendsto (h ∘ real_f) (𝓝[<] (1 : ℝ)) (𝓝 (target 1)) := by
    apply (target.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with t ht
    exact (real_target t ht).symm
  obtain ⟨left, leftK, left_target, tends_left⟩ := finite_fiber_right_limit real_f continuous_real
    K compactK real_contained h continuous_h (target 0) left_limit finite_left
  obtain ⟨right, rightK, right_target, tends_right⟩ := finite_fiber_left_limit real_f continuous_real
    K compactK real_contained h continuous_h (target 1) right_limit finite_right
  let G := extendFrom (Ioo (0 : ℝ) 1) real_f
  have continuous_G : ContinuousOn G (Icc 0 1) :=
    continuousOn_Icc_extendFrom_Ioo continuous_real tends_left tends_right
  have at_left : G 0 = left := eq_lim_at_left_extendFrom_Ioo (by norm_num) tends_left
  have at_right : G 1 = right := eq_lim_at_right_extendFrom_Ioo (by norm_num) tends_right
  have inside (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : G t = real_f t :=
    extendFrom_extends continuous_real t ht
  refine ⟨⟨fun t => G t, continuous_G.restrict⟩, ?_, ?_⟩
  · intro t
    exact (inside t t.property).trans (real_eq t)
  · intro t
    change G t ∈ K ∧ h (G t) = target t
    rcases eq_endpoints_or_mem_Ioo_of_mem_Icc t.property with left_end | right_end | interior
    · rw [left_end, at_left]
      exact ⟨leftK, left_target⟩
    · rw [right_end, at_right]
      exact ⟨rightK, right_target⟩
    · rw [inside t interior]
      exact ⟨real_contained t interior, real_target t interior⟩

end SixVertexUnfolding
