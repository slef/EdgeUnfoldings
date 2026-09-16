import SixVertexUnfolding.Geometry.SurfacePaths

/-! Arc length as a continuous parameter. This is the analytic input for
compactness of surface paths; it makes no nonoverlap assumption. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SurfacePath

open Set Filter
open scoped ENNReal NNReal Topology

variable {P : ConvexPolyhedron} {a b : Space}

/-- Computing variation directly on the unit interval gives the same path length. -/
theorem length_eq_variation (path : P.SurfacePath a b) :
    path.length = eVariationOn path.curve Set.univ := by
  have restriction : path.curve.extend ∘ ((↑) : unitInterval → ℝ) = path.curve := by
    funext t
    exact path.curve.extend_apply t.property
  have image : ((↑) : unitInterval → ℝ) '' Set.univ = Set.Icc 0 1 := by
    ext t
    simp
  rw [length, ← image, ← eVariationOn.comp_eq_of_monotoneOn _ _
    (show MonotoneOn ((↑) : unitInterval → ℝ) Set.univ from fun _ _ _ _ h => h), restriction]

/-- For a rectifiable continuous curve, distance travelled varies continuously.
Pauses are allowed: the accumulated length need not be strictly increasing. -/
theorem continuous_accumulated_length (f : unitInterval → Space)
    (continuous : Continuous f) (finite : BoundedVariationOn f Set.univ) :
    Continuous (variationOnFromTo f Set.univ 0) := by
  rw [continuous_iff_continuousAt]
  intro x
  apply continuousAt_iff_continuous_left_right.mpr
  refine ⟨?_, finite.continuousWithinAt_variationOnFromTo_Ici
    (continuous.continuousAt.continuousWithinAt)⟩
  have split : variationOnFromTo f Set.univ 0 =
      fun y => variationOnFromTo f Set.univ 0 x + variationOnFromTo f Set.univ x y := by
    funext y
    exact (variationOnFromTo.add finite.locallyBoundedVariationOn
      (mem_univ _) (mem_univ _) (mem_univ _)).symm
  rw [split]
  apply continuousWithinAt_const.add
  have vanishes := finite.tendsto_eVariationOn_Icc_zero_left
    (continuous.continuousAt.continuousWithinAt (s := Set.univ ∩ Iic x))
  have real_vanishes := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp vanishes
  have negative := real_vanishes.neg
  rw [nhdsWithin_univ] at negative
  have restricted := negative.mono_left (nhdsWithin_le_nhds (s := Iic x))
  simpa only [ContinuousWithinAt, ENNReal.toReal_zero, neg_zero, variationOnFromTo.self] using
    restricted.congr' (by
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (variationOnFromTo.eq_of_ge f Set.univ hy).symm)

/-- The accumulated length covers the entire interval from zero to total length. -/
theorem accumulated_length_image (f : unitInterval → Space)
    (continuous : Continuous f) (finite : BoundedVariationOn f Set.univ) :
    variationOnFromTo f Set.univ 0 '' Set.univ =
      Set.Icc 0 (eVariationOn f Set.univ).toReal := by
  have endpoints : (Set.Icc (0 : unitInterval) 1) = Set.univ := by
    ext t
    exact ⟨fun _ => mem_univ _, fun _ => t.property⟩
  have image := ContinuousOn.image_Icc_of_monotoneOn (show (0 : unitInterval) ≤ 1 from unitInterval.le_one')
    (continuous_accumulated_length f continuous finite).continuousOn
    ((variationOnFromTo.monotoneOn finite.locallyBoundedVariationOn (mem_univ 0)).mono
      (subset_univ _))
  rw [variationOnFromTo.self, variationOnFromTo.eq_of_le _ _ unitInterval.le_one',
    endpoints, inter_univ] at image
  exact image

/-- A curve parameterized by distance travelled is 1-Lipschitz. -/
theorem unit_speed_lipschitz {g : ℝ → Space} {s : Set ℝ}
    (speed : HasUnitSpeedOn g s) : LipschitzOnWith 1 g s := by
  intro x hx y hy
  wlog ordered : x ≤ y generalizing x y
  · simpa only [edist_comm] using this hy hx (le_of_not_ge ordered)
  have bound := eVariationOn.edist_le g
    (show x ∈ s ∩ Icc x y from ⟨hx, le_rfl, ordered⟩)
    (show y ∈ s ∩ Icc x y from ⟨hy, ordered, le_rfl⟩)
  rw [speed hx hy] at bound
  simpa only [NNReal.coe_one, one_mul, ENNReal.coe_one, edist_dist, Real.dist_eq,
    abs_sub_comm x y, abs_of_nonneg (sub_nonneg.mpr ordered)] using bound

end SixVertexUnfolding.ConvexPolyhedron.SurfacePath
