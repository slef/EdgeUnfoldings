import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Tactic.Linarith

/-! A circle covered by finitely many nonexpanding interval images has
circumference at most the sum of the interval lengths. -/

namespace SixVertexUnfolding

open Set MeasureTheory
open scoped ENNReal

/-- A nonexpanding interval image fits in the ball about its midpoint image. -/
theorem interval_image_in_midpoint_ball {Y : Type*} [MetricSpace Y]
    (f : ℝ → Y) (a b : ℝ) (ordered : a ≤ b)
    (nonexpanding : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, dist (f x) (f y) ≤ dist x y) :
    f '' Icc a b ⊆ Metric.closedBall (f ((a + b) / 2)) ((b - a) / 2) := by
  rintro _ ⟨x, hx, rfl⟩
  have midpoint : (a + b) / 2 ∈ Icc a b := ⟨by linarith, by linarith⟩
  apply (nonexpanding x hx _ midpoint).trans
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith [hx.1, hx.2]

/-- The ordinary circle measure of such an image is at most its interval length. -/
theorem circle_interval_image_volume (T : ℝ) [Fact (0 < T)]
    (f : ℝ → AddCircle T) (a b : ℝ) (ordered : a ≤ b)
    (nonexpanding : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, dist (f x) (f y) ≤ dist x y) :
    volume (f '' Icc a b) ≤ ENNReal.ofReal (b - a) := by
  calc
    volume (f '' Icc a b) ≤ volume (Metric.closedBall (f ((a + b) / 2)) ((b - a) / 2)) :=
      measure_mono (interval_image_in_midpoint_ball f a b ordered nonexpanding)
    _ = ENNReal.ofReal (min T (b - a)) := by
      rw [AddCircle.volume_closedBall]
      congr 2
      ring
    _ ≤ ENNReal.ofReal (b - a) := ENNReal.ofReal_le_ofReal (min_le_right _ _)

/-- Finite nonexpanding arcs cannot cover a circle of greater total length. -/
theorem circle_cover_length {ι : Type*} [Fintype ι] (T : ℝ) [Fact (0 < T)]
    (f : ι → ℝ → AddCircle T) (a b : ι → ℝ)
    (ordered : ∀ i, a i ≤ b i)
    (nonexpanding : ∀ i, ∀ x ∈ Icc (a i) (b i), ∀ y ∈ Icc (a i) (b i),
      dist (f i x) (f i y) ≤ dist x y)
    (covers : ∀ z : AddCircle T, ∃ i, z ∈ f i '' Icc (a i) (b i)) :
    T ≤ ∑ i, (b i - a i) := by
  have cover : (univ : Set (AddCircle T)) = ⋃ i, f i '' Icc (a i) (b i) := by
    ext z
    simpa using covers z
  have estimate : ENNReal.ofReal T ≤ ENNReal.ofReal (∑ i, (b i - a i)) := by
    calc
      ENNReal.ofReal T = volume (univ : Set (AddCircle T)) := (AddCircle.measure_univ T).symm
      _ = volume (⋃ i, f i '' Icc (a i) (b i)) := congrArg volume cover
      _ ≤ ∑ i, volume (f i '' Icc (a i) (b i)) := by
        simpa only [tsum_fintype] using measure_iUnion_le (fun i => f i '' Icc (a i) (b i))
      _ ≤ ∑ i, ENNReal.ofReal (b i - a i) :=
        Finset.sum_le_sum (fun i _ => circle_interval_image_volume T (f i) (a i) (b i)
          (ordered i) (nonexpanding i))
      _ = ENNReal.ofReal (∑ i, (b i - a i)) :=
        (ENNReal.ofReal_sum_of_nonneg (fun i _ => sub_nonneg.mpr (ordered i))).symm
  exact (ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg (fun i _ =>
    sub_nonneg.mpr (ordered i)))).mp estimate

end SixVertexUnfolding
