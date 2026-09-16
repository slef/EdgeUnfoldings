import SixVertexUnfolding.Definitions

/-! A planar circle stays connected after one point is removed. This is
the elementary topological input for ruling out one-branch Voronoi endings. -/

namespace SixVertexUnfolding

open Set

/-- Translation and positive scaling identify an arbitrary planar circle with the unit circle. -/
theorem planar_circle_homeomorph (z : Plane) (r : ℝ) (positive : 0 < r) :
    Nonempty (Metric.sphere (0 : Plane) 1 ≃ₜ Metric.sphere z r) := by
  let h : Plane ≃ₜ Plane := (Homeomorph.smulOfNeZero r positive.ne').trans (Homeomorph.addLeft z)
  refine ⟨h.subtype (fun x => ?_)⟩
  change dist x 0 = 1 ↔ dist (z + r • x) z = r
  rw [dist_eq_norm, sub_zero, dist_eq_norm, add_sub_cancel_left, norm_smul,
    Real.norm_eq_abs, abs_of_pos positive]
  constructor <;> intro equal <;> nlinarith

/-- Removing one point from a positive-radius planar circle leaves a preconnected set. -/
theorem punctured_planar_circle_preconnected (z : Plane) (r : ℝ) (positive : 0 < r)
    (w : Metric.sphere z r) : IsPreconnected (Metric.sphere z r \ {(w : Plane)}) := by
  obtain ⟨h⟩ := planar_circle_homeomorph z r positive
  let sphereMap := h.symm
  letI : Fact (Module.finrank ℝ Plane = 1 + 1) := ⟨by simp [Plane]⟩
  let chart := stereographic' 1 (sphereMap w)
  have source_iff (b : Metric.sphere z r) : b ≠ w ↔ sphereMap b ∈ chart.source := by
    simp only [chart, stereographic'_source, mem_compl_iff, mem_singleton_iff]
    exact not_congr sphereMap.injective.eq_iff.symm
  let puncture : {b : Metric.sphere z r // b ≠ w} ≃ₜ chart.source := sphereMap.subtype source_iff
  let target : chart.target ≃ₜ EuclideanSpace ℝ (Fin 1) :=
    (Homeomorph.setCongr (stereographic'_target (sphereMap w))).trans (Homeomorph.Set.univ _)
  let homeomorphism := (puncture.trans chart.toHomeomorphSourceTarget).trans target
  letI : ContractibleSpace {b : Metric.sphere z r // b ≠ w} := homeomorphism.contractibleSpace
  let f : {b : Metric.sphere z r // b ≠ w} → Plane := fun b => b.val.val
  have continuous_f : Continuous f := continuous_subtype_val.comp continuous_subtype_val
  have image : range f = Metric.sphere z r \ {(w : Plane)} := by
    ext x
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨b.val.property, fun same => b.property (Subtype.ext same)⟩
    · rintro ⟨member, different⟩
      exact ⟨⟨⟨x, member⟩, fun same => different (congrArg Subtype.val same)⟩, rfl⟩
  rw [← image]
  exact isPreconnected_range continuous_f

end SixVertexUnfolding
