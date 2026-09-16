import SixVertexUnfolding.Geometry.IntervalCenterBound

/-! Distance bounds on a finite closed cover extend along an interval.
No assumption on how often the curve crosses a piece boundary is needed. -/

namespace SixVertexUnfolding

open Set Filter Topology

/-- Near a point, only closed pieces containing that point can occur. -/
theorem finite_closed_cover_nearby {X ι : Type*} [TopologicalSpace X] [Finite ι]
    (pieces : ι → Set X) (closed : ∀ i, IsClosed (pieces i)) (x : X) :
    ∀ᶠ y in 𝓝 x, ∀ i, y ∈ pieces i → x ∈ pieces i := by
  classical
  apply Filter.eventually_all.mpr
  intro i
  by_cases member : x ∈ pieces i
  · exact Filter.Eventually.of_forall (fun _ _ => member)
  · filter_upwards [(closed i).isOpen_compl.mem_nhds member] with y hy hyi
    exact False.elim (hy hyi)

/-- A finite closed cover supplies the required distance bound at every nearby center. -/
theorem finite_closed_cover_center_bound {X Y ι : Type*} [MetricSpace X]
    [MetricSpace Y] [Finite ι] (s : Set X) (pieces : ι → Set X)
    (closed : ∀ i, IsClosed (pieces i)) (covers : s ⊆ ⋃ i, pieces i)
    (f : X → Y) (K : ℝ)
    (bounds : ∀ i, ∀ x ∈ s ∩ pieces i, ∀ y ∈ s ∩ pieces i,
      dist (f x) (f y) ≤ K * dist x y) (x : X) (hx : x ∈ s) :
    ∀ᶠ y in 𝓝[s] x, dist (f y) (f x) ≤ K * dist y x := by
  have nearby := (finite_closed_cover_nearby pieces closed x).filter_mono
    (nhdsWithin_le_nhds (s := s))
  filter_upwards [nearby, self_mem_nhdsWithin] with y hy ys
  obtain ⟨i, member⟩ := mem_iUnion.mp (covers ys)
  exact bounds i y ⟨ys, member⟩ x ⟨hx, hy i member⟩

/-- Piecewise nonexpansion gives nonexpansion along the whole interval. -/
theorem interval_distance_of_closed_cover {Y ι : Type*} [MetricSpace Y] [Finite ι]
    (f : ℝ → Y) (a b K : ℝ) (ordered : a ≤ b)
    (continuous_f : ContinuousOn f (Icc a b)) (pieces : ι → Set ℝ)
    (closed : ∀ i, IsClosed (pieces i)) (covers : Icc a b ⊆ ⋃ i, pieces i)
    (bounds : ∀ i, ∀ x ∈ Icc a b ∩ pieces i, ∀ y ∈ Icc a b ∩ pieces i,
      dist (f x) (f y) ≤ K * dist x y) :
    dist (f a) (f b) ≤ K * (b - a) :=
  interval_distance_of_center_bounds f a b K ordered continuous_f
    (finite_closed_cover_center_bound (Icc a b) pieces closed covers f K bounds)

/-- The same argument applies to every pair of parameters, not just the endpoints. -/
theorem interval_nonexpanding_of_closed_cover {Y ι : Type*} [MetricSpace Y] [Finite ι]
    (f : ℝ → Y) (a b : ℝ) (continuous_f : ContinuousOn f (Icc a b))
    (pieces : ι → Set ℝ) (closed : ∀ i, IsClosed (pieces i))
    (covers : Icc a b ⊆ ⋃ i, pieces i)
    (bounds : ∀ i, ∀ x ∈ Icc a b ∩ pieces i, ∀ y ∈ Icc a b ∩ pieces i,
      dist (f x) (f y) ≤ dist x y) :
    ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, dist (f x) (f y) ≤ dist x y := by
  have ordered_bound (x y : ℝ) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (ordered : x ≤ y) :
      dist (f x) (f y) ≤ y - x := by
    have subset : Icc x y ⊆ Icc a b := Icc_subset_Icc hx.1 hy.2
    simpa only [one_mul] using interval_distance_of_closed_cover f x y 1 ordered
      (continuous_f.mono subset) pieces closed (subset.trans covers)
      (fun i u hu v hv => by
        simpa only [one_mul] using bounds i u ⟨subset hu.1, hu.2⟩ v ⟨subset hv.1, hv.2⟩)
  intro x hx y hy
  rcases le_total x y with ordered | ordered
  · simpa only [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr ordered), neg_sub] using
      ordered_bound x y hx hy ordered
  · rw [dist_comm (f x) (f y)]
    simpa only [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ordered)] using
      ordered_bound y x hy hx ordered

end SixVertexUnfolding
