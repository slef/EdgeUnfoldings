import SixVertexUnfolding.Geometry.TriangleCones
import SixVertexUnfolding.Geometry.Separation

/-! Weak separating lines suffice for nonoverlap, even when entire closed cones touch along a boundary. -/

namespace SixVertexUnfolding

theorem translatedCone_height_lower (p e f : Plane) (height : Plane →L[ℝ] ℝ)
    (first : 0 ≤ height e) (second : 0 ≤ height f) :
    ∀ x ∈ translatedCone p e f, height p ≤ height x := by
  rintro x ⟨a, b, ha, hb, equal⟩
  have projected := congrArg height equal
  simp only [map_sub, map_add, map_smul, smul_eq_mul] at projected
  linarith [mul_nonneg ha first, mul_nonneg hb second]

/-- The two cones may share a boundary line; a nonconstant height still separates their interiors. -/
theorem opposed_cones_interiors_disjoint_of_height (p q e f g h : Plane) (height : Plane →L[ℝ] ℝ)
    (onto : Function.Surjective height) (base_nonpositive : height (q - p) ≤ 0)
    (he : 0 ≤ height e) (hf : 0 ≤ height f) (hg : 0 ≤ height g) (hh : 0 ≤ height h) :
    Disjoint (interior (translatedCone p e f)) (interior (translatedCone q (-g) (-h))) := by
  apply Disjoint.symm
  apply disjoint_interiors_of_halfplanes height onto (height p)
  · have negative_g : 0 ≤ (-height) (-g) := by simpa using hg
    have negative_h : 0 ≤ (-height) (-h) := by simpa using hh
    have bound := translatedCone_height_lower q (-g) (-h) (-height) negative_g negative_h
    intro x member
    have at_x := bound x member
    simp only [ContinuousLinearMap.neg_apply] at at_x
    rw [map_sub] at base_nonpositive
    linarith
  · exact translatedCone_height_lower p e f height he hf

end SixVertexUnfolding
