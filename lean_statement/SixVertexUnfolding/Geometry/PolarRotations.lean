import SixVertexUnfolding.Geometry.PlaneDistanceRigidity
import SixVertexUnfolding.Geometry.PlaneOrientation
import SixVertexUnfolding.Geometry.WedgeRotation

/-! Rotating the plane shifts the unwrapped angles in an explicit polar
wedge. The coordinate change is an actual linear isometry.
-/

namespace SixVertexUnfolding

open Real Set

/-- A genuine plane rotation adds the same real angle to every direction. -/
theorem exists_direction_rotation (τ : ℝ) :
    ∃ turn : Plane ≃ₗᵢ[ℝ] Plane, ∀ θ, turn (direction θ) = direction (θ + τ) := by
  have perpendicular : dist (direction 0) (direction (π / 2)) =
      dist (direction τ) (direction (τ + π / 2)) := by
    apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
    simp only [dist_eq_norm, norm_sub_sq_real, direction_norm, direction_inner]
    rw [show τ + π / 2 - τ = π / 2 by ring, sub_zero]
  obtain ⟨motion, origin, first, second⟩ := exists_plane_motion_triangle
    0 (direction 0) (direction (π / 2)) 0 (direction τ) (direction (τ + π / 2))
    (direction_ne_zero τ).symm (by simp only [dist_zero_left, direction_norm])
    (by simp only [dist_zero_left, direction_norm]) perpendicular
  have linear (x : Plane) : motion.linearIsometryEquiv x = motion x := by
    have identity := motion.map_vsub x 0
    simpa only [vsub_eq_sub, sub_zero, origin] using identity
  refine ⟨motion.linearIsometryEquiv, ?_⟩
  intro θ
  have axes : direction θ = cos θ • direction 0 + sin θ • direction (π / 2) := plane_eq_axes _
  rw [axes, map_add, map_smul, map_smul, linear, linear, first, second]
  ext i
  fin_cases i <;> simp [direction, PiLp.add_apply, PiLp.smul_apply, cos_add, sin_add] <;> ring

namespace Wedge

/-- Rotating a polar wedge is exactly a common shift of both arm angles. -/
theorem polarRegion_image_rotation (turn : Plane ≃ₗᵢ[ℝ] Plane) (τ : ℝ)
    (directions : ∀ θ, turn (direction θ) = direction (θ + τ))
    (d γ lower upper : ℝ) :
    turn '' polarRegion d γ lower upper = polarRegion d γ (lower + τ) (upper + τ) := by
  ext x
  constructor
  · rintro ⟨y, zero | ⟨ρ, θ, positive, position, low, high⟩, rfl⟩
    · rw [zero, map_zero]
      exact Or.inl rfl
    · right
      refine ⟨ρ, θ + τ, positive, ?_, by linarith, by linarith⟩
      rw [position, map_smul, directions]
  · rintro (zero | ⟨ρ, θ, positive, position, low, high⟩)
    · exact ⟨0, Or.inl rfl, by simpa using zero.symm⟩
    · refine ⟨ρ • direction (θ - τ), Or.inr ⟨ρ, θ - τ, positive, rfl,
        by linarith, by linarith⟩, ?_⟩
      rw [map_smul, directions, sub_add_cancel, ← position]

/-- Moving the angular cut by one full turn leaves the actual region unchanged. -/
theorem polarRegion_add_two_pi (d γ lower upper : ℝ) :
    polarRegion d γ (lower + 2 * π) (upper + 2 * π) = polarRegion d γ lower upper := by
  have directions (θ : ℝ) : (LinearIsometryEquiv.refl ℝ Plane) (direction θ) =
      direction (θ + 2 * π) := by
    ext i
    fin_cases i <;> simp [direction]
  simpa only [LinearIsometryEquiv.coe_refl, image_id] using
    (polarRegion_image_rotation (LinearIsometryEquiv.refl ℝ Plane) (2 * π) directions d γ lower upper).symm

end Wedge
end SixVertexUnfolding
