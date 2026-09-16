import SixVertexUnfolding.Definitions

/-! Finite affine pieces can be glued without increasing the speed bound.
This will lift straight segments through a finite developed vertex fan. -/

namespace SixVertexUnfolding

open Set Filter
open scoped Topology

variable {ι : Type*} [Finite ι]

/-- In a finite closed interval cover, some piece covers a right neighborhood of every nonfinal point. -/
theorem finite_closed_cover_right_interval (pieces : ι → Set ℝ)
    (closed : ∀ i, IsClosed (pieces i)) (convex : ∀ i, Convex ℝ (pieces i))
    (a b x : ℝ) (covered : Icc a b ⊆ ⋃ i, pieces i) (hx : x ∈ Ico a b) :
    ∃ i y, x < y ∧ Icc x y ⊆ pieces i := by
  let absent := {i : ι // x ∉ pieces i}
  let forbidden : Set ℝ := ⋃ i : absent, pieces i.val
  have closed_forbidden : IsClosed forbidden := isClosed_iUnion_of_finite (fun i => closed i.val)
  have outside : x ∈ forbiddenᶜ := by
    intro member
    obtain ⟨i, hi⟩ := mem_iUnion.mp member
    exact i.property hi
  have avoid : ∀ᶠ y in 𝓝 x, y ∈ forbiddenᶜ :=
    closed_forbidden.isOpen_compl.mem_nhds outside
  have before : ∀ᶠ y in 𝓝 x, y < b := Iio_mem_nhds hx.2
  have near := avoid.and before
  obtain ⟨y, xy, not_forbidden, before_b⟩ := near.exists_gt
  obtain ⟨i, yi⟩ := mem_iUnion.mp (covered ⟨hx.1.trans xy.le, before_b.le⟩)
  have xi : x ∈ pieces i := by
    by_contra absent_i
    exact not_forbidden (mem_iUnion.mpr ⟨⟨i, absent_i⟩, yi⟩)
  refine ⟨i, y, xy, ?_⟩
  rw [← segment_eq_Icc xy.le]
  exact (convex i).segment_subset xi yi

/-- Agreement with affine formulas on a finite closed cover gives continuity on its union. -/
theorem continuousOn_finite_affine_pieces (pieces : ι → Set ℝ)
    (closed : ∀ i, IsClosed (pieces i)) (maps : ι → ℝ →ᵃ[ℝ] Space) (f : ℝ → Space)
    (agrees : ∀ i, EqOn f (maps i) (pieces i)) : ContinuousOn f (⋃ i, pieces i) := by
  apply (locallyFinite_of_finite pieces).continuousOn_iUnion closed
  intro i
  exact (maps i).continuous_of_finiteDimensional.continuousOn.congr (agrees i)

/-- Every point before the end has the right derivative of one active affine piece. -/
theorem right_derivative_of_finite_affine_pieces (pieces : ι → Set ℝ)
    (closed : ∀ i, IsClosed (pieces i)) (convex : ∀ i, Convex ℝ (pieces i))
    (maps : ι → ℝ →ᵃ[ℝ] Space) (f : ℝ → Space) (agrees : ∀ i, EqOn f (maps i) (pieces i))
    (a b x : ℝ) (covered : Icc a b ⊆ ⋃ i, pieces i) (hx : x ∈ Ico a b) :
    ∃ i, HasDerivWithinAt f ((maps i).linear 1) (Ici x) x := by
  obtain ⟨i, y, xy, contained⟩ := finite_closed_cover_right_interval pieces closed convex a b x covered hx
  refine ⟨i, (maps i).hasDerivWithinAt.congr_of_eventuallyEq_of_mem ?_ (mem_Ici.mpr le_rfl)⟩
  filter_upwards [Icc_mem_nhdsGE xy] with t ht
  exact agrees i (contained ht)

/-- A common affine speed bound survives every crossing between finitely many closed convex pieces. -/
theorem finite_affine_pieces_distance_le (pieces : ι → Set ℝ)
    (closed : ∀ i, IsClosed (pieces i)) (convex : ∀ i, Convex ℝ (pieces i))
    (maps : ι → ℝ →ᵃ[ℝ] Space) (f : ℝ → Space) (agrees : ∀ i, EqOn f (maps i) (pieces i))
    (a b C : ℝ) (ordered : a ≤ b) (covered : Icc a b ⊆ ⋃ i, pieces i)
    (speed : ∀ i, ‖(maps i).linear 1‖ ≤ C) : dist (f a) (f b) ≤ C * (b - a) := by
  have continuous := (continuousOn_finite_affine_pieces pieces closed maps f agrees).mono covered
  have active (x : ℝ) (hx : x ∈ Ico a b) :=
    right_derivative_of_finite_affine_pieces pieces closed convex maps f agrees a b x covered hx
  have derivative (x : ℝ) (hx : x ∈ Ico a b) :
      HasDerivWithinAt f (derivWithin f (Ici x) x) (Ici x) x := by
    obtain ⟨i, hi⟩ := active x hx
    rwa [hi.derivWithin (uniqueDiffWithinAt_Ici x)]
  have bound (x : ℝ) (hx : x ∈ Ico a b) : ‖derivWithin f (Ici x) x‖ ≤ C := by
    obtain ⟨i, hi⟩ := active x hx
    rw [hi.derivWithin (uniqueDiffWithinAt_Ici x)]
    exact speed i
  have estimate := norm_image_sub_le_of_norm_deriv_right_le_segment continuous derivative bound b ⟨ordered, le_rfl⟩
  simpa only [← dist_eq_norm, dist_comm (f b)] using estimate

end SixVertexUnfolding
