import SixVertexUnfolding.Geometry.ArcLength

/-! Every rectifiable surface path can be traversed at bounded speed.
Endpoints and the actual surface image are preserved. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SurfacePath

open Set
open scoped ENNReal NNReal

variable {P : ConvexPolyhedron} {a b : Space}

/-- A speed bound on the unit interval is also a bound on total length. -/
theorem length_le_of_lipschitz (path : P.SurfacePath a b) {C : ℝ≥0}
    (speed : LipschitzWith C path.curve) : path.length ≤ C := by
  rw [path.length_eq_variation]
  have unit : eVariationOn (id : unitInterval → unitInterval) Set.univ ≤ 1 := by
    have same := eVariationOn.comp_eq_of_monotoneOn (id : ℝ → ℝ)
      ((↑) : unitInterval → ℝ) (show MonotoneOn ((↑) : unitInterval → ℝ) Set.univ
        from fun _ _ _ _ h => h)
    have distance : eVariationOn (id : unitInterval → unitInterval) Set.univ =
        eVariationOn ((↑) : unitInterval → ℝ) Set.univ := rfl
    rw [distance]
    have image : ((↑) : unitInterval → ℝ) '' Set.univ = Set.Icc 0 1 := by ext t; simp
    change eVariationOn ((id : ℝ → ℝ) ∘ ((↑) : unitInterval → ℝ)) Set.univ ≤ 1
    rw [same, image]
    simpa using (monotone_id.monotoneOn (s := Set.univ)).eVariationOn_le
      (mem_univ (0 : ℝ)) (mem_univ (1 : ℝ))
  have bound := speed.lipschitzOnWith.comp_eVariationOn_le
    (show MapsTo (id : unitInterval → unitInterval) Set.univ Set.univ from fun _ _ => mem_univ _)
  exact bound.trans (by simpa using mul_le_mul_right unit (C : ℝ≥0∞))

/-- Finite-length paths have a Lipschitz replacement with the same endpoints,
the same surface image, and no greater length. -/
theorem exists_lipschitz_reparameterization (path : P.SurfacePath a b)
    (finite : path.length ≠ ⊤) :
    ∃ replacement : P.SurfacePath a b,
      LipschitzWith path.length.toNNReal replacement.curve ∧
      Set.range replacement.curve = Set.range path.curve ∧
      replacement.length ≤ path.length := by
  have bounded : BoundedVariationOn path.curve Set.univ := by
    change eVariationOn path.curve Set.univ ≠ ⊤
    rwa [← path.length_eq_variation]
  let L := path.length.toReal
  let g := naturalParameterization path.curve Set.univ (0 : unitInterval)
  have covered : variationOnFromTo path.curve Set.univ 0 '' Set.univ = Icc 0 L := by
    simpa only [L, path.length_eq_variation] using
      accumulated_length_image path.curve path.curve.continuous bounded
  have same (t : unitInterval) :
      g (variationOnFromTo path.curve Set.univ 0 t) = path.curve t :=
    edist_eq_zero.mp (edist_naturalParameterization_eq_zero
      bounded.locallyBoundedVariationOn (mem_univ _) (mem_univ t))
  have natural_speed : LipschitzOnWith 1 g (Icc 0 L) := by
    rw [← covered]
    exact unit_speed_lipschitz (has_unit_speed_naturalParameterization _
      bounded.locallyBoundedVariationOn (mem_univ _))
  have in_interval (t : unitInterval) : L * (t : ℝ) ∈ Icc 0 L :=
    ⟨mul_nonneg ENNReal.toReal_nonneg t.property.1,
      mul_le_of_le_one_right ENNReal.toReal_nonneg t.property.2⟩
  let f : unitInterval → Space := fun t => g (L * (t : ℝ))
  have speed : LipschitzWith path.length.toNNReal f := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have bound := natural_speed.dist_le_mul _ (in_interval x) _ (in_interval y)
    simpa only [NNReal.coe_one, one_mul, Real.dist_eq, ← mul_sub, abs_mul,
      abs_of_nonneg (show 0 ≤ L from ENNReal.toReal_nonneg),
      ENNReal.coe_toNNReal_eq_toReal, Subtype.dist_eq, L] using bound
  have at_zero : f 0 = a := by
    change g (L * 0) = a
    simpa only [mul_zero, variationOnFromTo.self, Path.source] using same 0
  have at_one : f 1 = b := by
    have end_length : variationOnFromTo path.curve Set.univ 0 1 = L := by
      rw [variationOnFromTo.eq_of_le _ _ unitInterval.le_one']
      have interval : Icc (0 : unitInterval) 1 = Set.univ := by
        ext t; exact ⟨fun _ => mem_univ _, fun _ => t.property⟩
      rw [interval, inter_univ, ← path.length_eq_variation]
    change g (L * 1) = b
    simpa only [mul_one, end_length, Path.target] using same 1
  have image : Set.range f = Set.range path.curve := by
    apply Subset.antisymm
    · rintro _ ⟨t, rfl⟩
      obtain ⟨u, _, hu⟩ := covered ▸ in_interval t
      exact ⟨u, by change path.curve u = g (L * (t : ℝ)); rw [← hu, same]⟩
    · rintro _ ⟨t, rfl⟩
      by_cases zero : L = 0
      · refine ⟨0, ?_⟩
        have h := covered ▸ mem_image_of_mem (variationOnFromTo path.curve Set.univ 0) (mem_univ t)
        have ht : variationOnFromTo path.curve Set.univ 0 t = 0 := by simpa [zero] using h
        change g (L * 0) = path.curve t
        simpa only [mul_zero, ht] using same t
      · let s := variationOnFromTo path.curve Set.univ 0 t
        have hs : s ∈ Icc 0 L := covered ▸ mem_image_of_mem _ (mem_univ t)
        have positive : 0 < L := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm zero)
        refine ⟨⟨s / L, div_nonneg hs.1 positive.le, (div_le_one positive).mpr hs.2⟩, ?_⟩
        change g (L * (s / L)) = path.curve t
        rw [mul_div_cancel₀ _ zero]
        exact same t
  let replacement : P.SurfacePath a b :=
    ⟨⟨⟨f, speed.continuous⟩, at_zero, at_one⟩, fun t => by
      obtain ⟨u, hu⟩ := image ▸ mem_range_self t
      change f t ∈ frontier P.body
      exact hu ▸ path.on_surface u⟩
  refine ⟨replacement, speed, image, ?_⟩
  exact (replacement.length_le_of_lipschitz speed).trans_eq (ENNReal.coe_toNNReal finite)

end SixVertexUnfolding.ConvexPolyhedron.SurfacePath
