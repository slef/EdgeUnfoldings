import SixVertexUnfolding.Geometry.HingeSideOrder
import SixVertexUnfolding.Geometry.FacetCornerCone
import SixVertexUnfolding.Geometry.FacetHingeSides
import SixVertexUnfolding.Geometry.LocalFacetHalfspaces

/-! Signed heights describe both sides of a developed hinge, including the
extended facet planes needed for local flat neighborhoods. -/

namespace SixVertexUnfolding

open Set

/-- Vanishing perpendicular component means membership in the full hinge line. -/
theorem hingeSideVector_eq_zero_iff_line (a b x : Plane) (different : a ≠ b) :
    hingeSideVector a b x = 0 ↔ x ∈ affineSpan ℝ ({a, b} : Set Plane) := by
  constructor
  · intro zero
    have expression : x - a = inner ℝ (NormedSpace.normalize (b - a)) (x - a) •
        NormedSpace.normalize (b - a) := sub_eq_zero.mp zero
    apply mem_affineSpan_pair_iff_exists_lineMap_eq.mpr
    refine ⟨inner ℝ (NormedSpace.normalize (b - a)) (x - a) * ‖b - a‖⁻¹, ?_⟩
    have scaled (r : ℝ) : r • NormedSpace.normalize (b - a) = (r * ‖b - a‖⁻¹) • (b - a) := by
      rw [NormedSpace.normalize, smul_smul]
    rw [scaled] at expression
    rw [AffineMap.lineMap_apply_module', ← expression, sub_add_cancel]
  · intro member
    obtain ⟨t, rfl⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp member
    rw [AffineMap.lineMap_apply_module']
    change hingeRemainder (NormedSpace.normalize (b - a)) ((t • (b - a) + a) - a) = 0
    rw [add_sub_cancel_right]
    have unit := NormedSpace.norm_normalize (sub_ne_zero.mpr different.symm : b - a ≠ 0)
    have scaled : t • (b - a) = (t * ‖b - a‖) • NormedSpace.normalize (b - a) := by
      rw [← smul_smul, NormedSpace.norm_smul_normalize]
    rw [scaled]
    exact hingeRemainder_smul_axis unit _

/-- A nonzero transverse reference defines precisely the hinge line as its zero-height set. -/
theorem hinge_height_zero_iff_line (a b reference x : Plane) (different : a ≠ b)
    (nonzero : hingeSideVector a b reference ≠ 0) :
    inner ℝ (hingeSideVector a b reference) (x - a) = 0 ↔
      x ∈ affineSpan ℝ ({a, b} : Set Plane) := by
  let axis := NormedSpace.normalize (b - a)
  have unit : ‖axis‖ = 1 := NormedSpace.norm_normalize (sub_ne_zero.mpr different.symm)
  have axis_ne : axis ≠ 0 := by intro zero; simp [zero] at unit
  have orthogonal (z : Plane) : inner ℝ axis (hingeSideVector a b z) = 0 :=
    hingeRemainder_orthogonal unit (z - a)
  obtain ⟨t, multiple⟩ := perpendicular_multiple axis (hingeSideVector a b reference)
    (hingeSideVector a b x) axis_ne nonzero (orthogonal reference) (orthogonal x)
  rw [hingeSideVector_inner a b reference x different, ← hingeSideVector_eq_zero_iff_line a b x different]
  constructor
  · intro zero
    rw [multiple, inner_smul_right, real_inner_self_eq_norm_sq] at zero
    have t_zero : t = 0 := (mul_eq_zero.mp zero).resolve_right (pow_ne_zero 2 (norm_ne_zero_iff.mpr nonzero))
    rw [multiple, t_zero, zero_smul]
  · intro zero
    rw [zero, inner_zero_right]

/-- Nonzero opposite transverse normals differ by a strictly negative factor. -/
theorem opposite_hinge_height_factor (a b reference other : Plane) (different : a ≠ b)
    (first_nonzero : hingeSideVector a b reference ≠ 0)
    (second_nonzero : hingeSideVector a b other ≠ 0)
    (opposite : OppositeHingeSides a b reference other) :
    ∃ t : ℝ, t < 0 ∧ ∀ x, inner ℝ (hingeSideVector a b other) (x - a) =
      t * inner ℝ (hingeSideVector a b reference) (x - a) := by
  let axis := NormedSpace.normalize (b - a)
  have unit : ‖axis‖ = 1 := NormedSpace.norm_normalize (sub_ne_zero.mpr different.symm)
  have axis_ne : axis ≠ 0 := by intro zero; simp [zero] at unit
  obtain ⟨t, multiple⟩ := perpendicular_multiple axis (hingeSideVector a b reference)
    (hingeSideVector a b other) axis_ne first_nonzero
    (hingeRemainder_orthogonal unit _) (hingeRemainder_orthogonal unit _)
  have nonzero : t ≠ 0 := by intro zero; exact second_nonzero (by rw [multiple, zero, zero_smul])
  change inner ℝ (hingeSideVector a b reference) (hingeSideVector a b other) ≤ 0 at opposite
  rw [multiple, inner_smul_right, real_inner_self_eq_norm_sq] at opposite
  have positive : 0 < ‖hingeSideVector a b reference‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr first_nonzero)
  refine ⟨t, lt_of_le_of_ne (by nlinarith) nonzero, ?_⟩
  intro x
  rw [multiple, real_inner_smul_left]

namespace ConvexPolyhedron.Face

/-- A neighboring support inequality becomes the inward planar half-plane after a rigid placement. -/
theorem support_iff_hinge_height {P : ConvexPolyhedron} {center : Space}
    (facets : P.NormalizedFacets center) (F G : P.Face) (a b c : Space)
    (aF : a ∈ F.val) (bF : b ∈ F.val) (cF : c ∈ F.val)
    (aG : a ∈ G.val) (bG : b ∈ G.val) (cG : c ∉ G.val)
    (noncollinear : ¬ Collinear ℝ ({a, b, c} : Set Space))
    (place : Space →ᵃ[ℝ] Plane) (different : place a ≠ place b)
    (transverse : hingeSideVector (place a) (place b) (place c) ≠ 0)
    (x : Space) (x_plane : x ∈ affineSpan ℝ F.val) :
    inner ℝ (facets.normal G) (x - center) ≤ 1 ↔
      0 ≤ inner ℝ (hingeSideVector (place a) (place b) (place c)) (place x - place a) := by
  obtain ⟨t, u, coordinates⟩ := F.plane_triangle_coordinates_of_mem_plane a b c x
    (subset_affineSpan ℝ _ aF) (subset_affineSpan ℝ _ bF) (subset_affineSpan ℝ _ cF)
    noncollinear x_plane
  have at_a := facets.on_face G aG
  have at_b := facets.on_face G bG
  have at_c := facets.strict_of_not_mem_face G (F.subset_body cF) cG
  have measured := congrArg (fun v => inner ℝ (facets.normal G) v) coordinates
  simp only [inner_add_right, inner_smul_right, inner_sub_right] at measured
  have value : inner ℝ (facets.normal G) (x - center) - 1 =
      u * (inner ℝ (facets.normal G) (c - center) - 1) := by
    rw [inner_sub_right] at at_a at_b ⊢
    rw [inner_sub_right]
    linear_combination measured + (1 - u - t) * at_a + t * at_b
  have flat := hingeSideVector_of_coordinates place a b c x t u coordinates different
  rw [hingeSideVector_inner _ _ _ _ different, flat, inner_smul_right, real_inner_self_eq_norm_sq]
  have positive : 0 < ‖hingeSideVector (place a) (place b) (place c)‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr transverse)
  constructor <;> intro bound
  · have nonnegative : 0 ≤ u := by nlinarith
    exact mul_nonneg nonnegative positive.le
  · have nonnegative : 0 ≤ u := by nlinarith
    nlinarith [mul_nonpos_of_nonneg_of_nonpos nonnegative (sub_nonpos.mpr at_c.le)]

end ConvexPolyhedron.Face
end SixVertexUnfolding
