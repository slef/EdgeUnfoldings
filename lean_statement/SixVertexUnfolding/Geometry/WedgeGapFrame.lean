import SixVertexUnfolding.Geometry.WedgeGapRotation
import SixVertexUnfolding.Geometry.WedgeCoordinates

/-! A gap's two source copies and its bisecting cut ray admit exactly the
Cartesian frame used in the wedge step. The plane map is a rigid motion.
-/

namespace SixVertexUnfolding.Wedge

open Real Set

/-- A rotation followed by a translation transports a root-centered region
by the corresponding linear rotation. -/
theorem translated_region_image (z c : Plane) (turn : Plane ≃ₗᵢ[ℝ] Plane)
    (frame : Plane ≃ᵃⁱ[ℝ] Plane) (formula : ∀ x, frame x = turn (x - z) + c)
    (S : Set Plane) :
    frame '' {x | x - z ∈ S} = {x | x - c ∈ turn '' S} := by
  ext x
  constructor
  · rintro ⟨y, member, rfl⟩
    exact ⟨y - z, member, by rw [formula, add_sub_cancel_right]⟩
  · rintro ⟨v, member, located⟩
    refine ⟨v + z, by simpa using member, ?_⟩
    rw [formula, add_sub_cancel_right, located, sub_add_cancel]

/-- The outgoing gap becomes the pair `(0,±h)`, with its ray horizontal.
The old root and every point of the outgoing ray have explicit coordinates. -/
theorem gap_frame (z : Plane) {d γ δ : ℝ} (positive : 0 < d)
    (ordered : γ < δ) (width : δ < γ + 2 * π)
    (turn : Plane ≃ₗᵢ[ℝ] Plane)
    (directions : ∀ φ, turn (direction φ) = direction (φ - (γ + δ) / 2)) :
    let θ := (δ - γ) / 2
    let h := d * sin θ
    let r := -d * cos θ
    0 < h ∧ 0 < θ ∧ θ < π ∧
      ∃ frame : Plane ≃ᵃⁱ[ℝ] Plane,
        (∀ x, frame x = turn (x - z) + point r 0) ∧
        frame z = point r 0 ∧
        frame (z + d • direction γ) = point 0 (-h) ∧
        frame (z + d • direction δ) = point 0 h ∧
        ∀ L : ℝ, frame (z + L • direction ((γ + δ) / 2)) = point (r + L) 0 := by
  dsimp only
  have angle_positive : 0 < (δ - γ) / 2 := by linarith
  have angle_small : (δ - γ) / 2 < π := by linarith
  let r := -d * cos ((δ - γ) / 2)
  let frame := ((AffineIsometryEquiv.vaddConst ℝ z).symm.trans
    turn.toAffineIsometryEquiv).trans (AffineIsometryEquiv.vaddConst ℝ (point r 0))
  have formula (x : Plane) : frame x = turn (x - z) + point r 0 := rfl
  refine ⟨mul_pos positive (sin_pos_of_pos_of_lt_pi angle_positive angle_small),
    angle_positive, angle_small, frame, formula, ?_, ?_, ?_, ?_⟩
  · rw [formula, sub_self, map_zero, zero_add]
  · rw [formula, add_sub_cancel_left, map_smul, directions,
      show γ - (γ + δ) / 2 = -((δ - γ) / 2) by ring]
    ext i
    fin_cases i <;> simp [r, point, direction, PiLp.add_apply, PiLp.smul_apply, add_comm]
  · rw [formula, add_sub_cancel_left, map_smul, directions,
      show δ - (γ + δ) / 2 = (δ - γ) / 2 by ring]
    ext i
    fin_cases i <;> simp [r, point, direction, PiLp.add_apply, PiLp.smul_apply, add_comm]
  · intro L
    rw [formula, add_sub_cancel_left, map_smul, directions, sub_self]
    ext i
    fin_cases i <;> simp [r, point, direction, PiLp.add_apply, PiLp.smul_apply, add_comm]

/-- The explicit gap frame satisfies the existing Cartesian/polar wedge
coordinate record for every permitted outer-leg angle. -/
theorem gap_arm_coordinates {d γ δ ω : ℝ} (positive : 0 < d)
    (ordered : γ < δ) (width : δ < γ + 2 * π)
    (lower : π / 2 ≤ ω) (upper : ω ≤ 3 * π / 2) :
    let θ := (δ - γ) / 2
    ArmCoordinates (d * sin θ) (-d * cos θ)
      (d * cos (θ + (π - ω))) (d * sin (θ + (π - ω))) d θ ω := by
  exact ⟨positive, by linarith, by linarith, lower, upper, by ring, rfl, rfl, rfl⟩

end SixVertexUnfolding.Wedge
