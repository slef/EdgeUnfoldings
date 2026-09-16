import SixVertexUnfolding.Geometry.HingeCoordinates
import SixVertexUnfolding.Geometry.HingePlacement

/-! Choose the outward side when aligning two triangles along an original hinge. -/

namespace SixVertexUnfolding

/-- The component perpendicular to the hinge line, measured from its first endpoint. -/
noncomputable def hingeSideVector (a b x : Plane) : Plane :=
  hingeRemainder (NormedSpace.normalize (b - a)) (x - a)

/-- The two free vertices lie on opposite closed sides of the hinge line. -/
def OppositeHingeSides (a b x y : Plane) : Prop :=
  inner ℝ (hingeSideVector a b x) (hingeSideVector a b y) ≤ 0

theorem hingeSideVector_left (a b : Plane) : hingeSideVector a b a = 0 := by
  simp [hingeSideVector, hingeRemainder]

theorem hingeRemainder_smul_axis {axis : Plane} (unit : ‖axis‖ = 1) (t : ℝ) :
    hingeRemainder axis (t • axis) = 0 := by
  simp [hingeRemainder, inner_smul_right, unit]

theorem hingeSideVector_right (a b : Plane) (distinct : a ≠ b) : hingeSideVector a b b = 0 := by
  have unit := NormedSpace.norm_normalize (sub_ne_zero.mpr distinct.symm : b - a ≠ 0)
  change hingeRemainder (NormedSpace.normalize (b - a)) (b - a) = 0
  nth_rw 2 [← NormedSpace.norm_smul_normalize (b - a)]
  exact hingeRemainder_smul_axis unit _

/-- Removing the other point's hinge component does not change this perpendicular height. -/
theorem hingeSideVector_inner (a b c x : Plane) (distinct : a ≠ b) :
    inner ℝ (hingeSideVector a b c) (x - a) =
      inner ℝ (hingeSideVector a b c) (hingeSideVector a b x) := by
  have unit := NormedSpace.norm_normalize (sub_ne_zero.mpr distinct.symm : b - a ≠ 0)
  have zero := hingeRemainder_orthogonal unit (c - a)
  have zero' : inner ℝ (hingeSideVector a b c) (NormedSpace.normalize (b - a)) = 0 := by
    simpa only [hingeSideVector, real_inner_comm] using zero
  simp only [hingeSideVector, hingeRemainder, inner_sub_right, inner_smul_right] at zero' ⊢
  rw [zero', mul_zero, sub_zero]

/-- A free point not on the hinge line gives a nonzero separating normal. -/
theorem hingeSideVector_ne_zero (a b c : Plane)
    (noncollinear : ¬ Collinear ℝ ({a, b, c} : Set Plane)) : hingeSideVector a b c ≠ 0 := by
  intro zero
  have same : c - a = inner ℝ (NormedSpace.normalize (b - a)) (c - a) •
      NormedSpace.normalize (b - a) := sub_eq_zero.mp zero
  apply noncollinear
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  refine ⟨a, b - a, ?_⟩
  intro p hp
  rcases hp with hp | hp | hp
  · subst p
    exact ⟨0, by simp⟩
  · subst p
    exact ⟨1, by simp⟩
  · have equal : p = c := hp
    subst p
    refine ⟨inner ℝ (NormedSpace.normalize (b - a)) (c - a) * ‖b - a‖⁻¹, ?_⟩
    rw [NormedSpace.normalize, smul_smul] at same
    simpa using (eq_add_of_sub_eq same)

/-- Reflection in a unit hinge reverses the perpendicular component. -/
theorem hingeRemainder_reflection {axis : Plane} (unit : ‖axis‖ = 1) (y : Plane) :
    hingeRemainder axis ((Submodule.span ℝ {axis}).reflection y) = -hingeRemainder axis y := by
  have formula := Submodule.reflection_apply (K := Submodule.span ℝ {axis}) y
  rw [Submodule.starProjection_unit_singleton ℝ unit] at formula
  rw [formula]
  simp only [hingeRemainder, two_smul, inner_add_right, inner_sub_right, inner_smul_right,
    real_inner_self_eq_norm_sq, unit, one_pow, mul_one]
  module

/-- Either the current placement or its mirror puts a free vertex opposite the base vertex. -/
theorem exists_opposite_hinge_motion (a b x y : Plane) (distinct : a ≠ b) :
    ∃ motion : Plane ≃ᵃⁱ[ℝ] Plane, motion a = a ∧ motion b = b ∧
      OppositeHingeSides a b x (motion y) := by
  by_cases opposite : OppositeHingeSides a b x y
  · exact ⟨AffineIsometryEquiv.refl ℝ Plane, rfl, rfl, opposite⟩
  let axis := NormedSpace.normalize (b - a)
  have unit : ‖axis‖ = 1 := NormedSpace.norm_normalize (sub_ne_zero.mpr distinct.symm)
  let turn := (Submodule.span ℝ {axis}).reflection
  let motion := ((AffineIsometryEquiv.vaddConst ℝ a).symm.trans
    turn.toAffineIsometryEquiv).trans (AffineIsometryEquiv.vaddConst ℝ a)
  have formula (p : Plane) : motion p = turn (p - a) + a := rfl
  have hinge_fixed : turn (b - a) = b - a := by
    apply Submodule.reflection_mem_subspace_eq_self
    exact Submodule.mem_span_singleton.mpr ⟨‖b - a‖, NormedSpace.norm_smul_normalize _⟩
  refine ⟨motion, ?_, ?_, ?_⟩
  · rw [formula, sub_self, map_zero, zero_add]
  · rw [formula, hinge_fixed, sub_add_cancel]
  · have reversed : hingeSideVector a b (motion y) = -hingeSideVector a b y := by
      rw [hingeSideVector, formula, add_sub_cancel_right]
      exact hingeRemainder_reflection unit (y - a)
    change inner ℝ (hingeSideVector a b x) (hingeSideVector a b (motion y)) ≤ 0
    rw [reversed, inner_neg_right]
    exact neg_nonpos.mpr (le_of_not_ge opposite)

end SixVertexUnfolding
