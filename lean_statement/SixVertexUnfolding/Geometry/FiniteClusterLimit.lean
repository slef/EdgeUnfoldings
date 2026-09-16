import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Order.Interval.Set.Infinite

/-! A continuous curve in a compact metric set has a one-sided limit
if only finitely many points can be cluster points at that endpoint. -/

namespace SixVertexUnfolding

open Set Filter Topology Metric

/-- A continuous curve cannot oscillate between finitely many possible endpoint limits. -/
theorem finite_cluster_right_limit {Y : Type*} [MetricSpace Y] (f : ℝ → Y)
    (continuous_f : ContinuousOn f (Ioo 0 1)) (K : Set Y) (compactK : IsCompact K)
    (contained : ∀ t ∈ Ioo (0 : ℝ) 1, f t ∈ K)
    (F : Set Y) (finiteF : F.Finite)
    (cluster_in_F : ∀ y ∈ K, MapClusterPt y (𝓝[>] (0 : ℝ)) f → y ∈ F) :
    ∃ y ∈ F, Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 y) := by
  have eventualK : ∀ᶠ t in 𝓝[>] (0 : ℝ), f t ∈ K := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with t ht using contained t ht
  have compact_filter : map f (𝓝[>] (0 : ℝ)) ≤ 𝓟 K := le_principal_iff.mpr eventualK
  obtain ⟨p, pK, cluster_p⟩ := compactK.exists_mapClusterPt compact_filter
  refine ⟨p, cluster_in_F p pK cluster_p, compactK.tendsto_nhds_of_unique_mapClusterPt eventualK ?_⟩
  intro q qK cluster_q
  by_contra different
  have positive : 0 < dist p q := dist_pos.mpr (Ne.symm different)
  obtain ⟨r, radius, avoids⟩ := (Ioo_infinite positive).exists_notMem_finite (finiteF.image (dist p))
  have eventual_avoid : ∀ᶠ t in 𝓝[>] (0 : ℝ), dist p (f t) ≠ r := by
    apply compactK.adherence_nhdset compact_filter
      (isOpen_ne_fun (continuous_const.dist continuous_id) continuous_const)
    intro y yK cluster_y equal
    exact avoids ⟨y, cluster_in_F y yK cluster_y, equal⟩
  obtain ⟨δ, positiveδ, avoids_on⟩ := (nhdsGT_basis (0 : ℝ)).mem_iff.mp eventual_avoid
  let ε := min δ 1
  have positiveε : 0 < ε := lt_min positiveδ (by norm_num)
  have interval : Ioo (0 : ℝ) ε ⊆ Ioo 0 1 := fun t ht => ⟨ht.1, ht.2.trans_le (min_le_right _ _)⟩
  have avoids_on' : ∀ t ∈ Ioo (0 : ℝ) ε, dist p (f t) ≠ r :=
    fun t ht => avoids_on ⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩
  have sides := isPreconnected_Ioo.mapsTo_Ioi_or_Iio
    (((continuous_const.dist continuous_id).comp_continuousOn continuous_f).mono interval) avoids_on'
  have near_p : ∃ᶠ t in 𝓝[>] (0 : ℝ), dist p (f t) < r :=
    cluster_p.frequently ((isOpen_lt (continuous_const.dist continuous_id) continuous_const).mem_nhds
      (by simpa using radius.1))
  have near_q : ∃ᶠ t in 𝓝[>] (0 : ℝ), r < dist p (f t) :=
    cluster_q.frequently ((isOpen_lt continuous_const (continuous_const.dist continuous_id)).mem_nhds radius.2)
  rcases sides with above | below
  · obtain ⟨t, ht, inside⟩ := (near_p.and_eventually (Ioo_mem_nhdsGT positiveε)).exists
    exact (above inside).not_gt ht
  · obtain ⟨t, ht, inside⟩ := (near_q.and_eventually (Ioo_mem_nhdsGT positiveε)).exists
    exact (below inside).not_gt ht

end SixVertexUnfolding
