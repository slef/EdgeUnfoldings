import SixVertexUnfolding.Geometry.ContactSineGeometry

/-! The same finite-contact sine data with clockwise copied-edge directions. -/

namespace SixVertexUnfolding.Contact

open Real

theorem polar_contact_sine_data_clockwise (a m p : Plane) (r s R ω Γ δ θ gap t : ℝ)
    (r_nonnegative : 0 ≤ r) (sine_nonnegative : 0 ≤ sin δ)
    (turn : ω + δ = Γ + 2 * π)
    (at_a : a = r • direction ω)
    (at_m : m - a = s • direction (ω + π - θ))
    (at_p : p - a = s • direction (ω + π - θ - gap))
    (contact : a + t • (p - a) ∈ segment ℝ 0 (R • direction Γ))
    (contained : m ∈ convexHull ℝ ({a, 0, a + t • (p - a)} : Set Plane)) :
    r * sin δ = t * s * sin (θ + gap + δ) ∧
      s * sin (θ + δ) ≤ r * sin δ := by
  have at_base : det (direction Γ) a = -(r * sin δ) := by
    rw [at_a, det_smul_right, direction_det,
      show ω - Γ = -δ + 2 * π by linarith, sin_add_two_pi, sin_neg]
    ring
  have at_copy : det (direction Γ) (m - a) = s * sin (θ + δ) := by
    rw [at_m, det_smul_right, direction_det,
      show ω + π - θ - Γ = (π - (θ + δ)) + 2 * π by linarith,
      sin_add_two_pi, sin_pi_sub]
  have at_cut : det (direction Γ) (p - a) = s * sin (θ + gap + δ) := by
    rw [at_p, det_smul_right, direction_det,
      show ω + π - θ - gap - Γ = (π - (θ + gap + δ)) + 2 * π by linarith,
      sin_add_two_pi, sin_pi_sub]
  have on_line := radial_segment_det_zero Γ R _ contact
  have contact_eq : r * sin δ = t * s * sin (θ + gap + δ) := by
    rw [det_add_right, det_smul_right, at_base, at_cut] at on_line
    nlinarith
  have nonpositive : det (direction Γ) m ≤ 0 := by
    let height := detHeight (direction Γ)
    have inclusion : convexHull ℝ ({a, 0, a + t • (p - a)} : Set Plane) ⊆ {x | height x ≤ 0} := by
      apply convexHull_min _ ((convex_Iic (0 : ℝ)).linear_preimage height.toLinearMap)
      rintro x (rfl | rfl | rfl)
      · change det (direction Γ) _ ≤ 0
        rw [at_base]
        exact neg_nonpos.mpr (mul_nonneg r_nonnegative sine_nonnegative)
      · change det (direction Γ) 0 ≤ 0
        simp [det]
      · change det (direction Γ) (a + t • (p - a)) ≤ 0
        exact on_line.le
    exact inclusion contained
  have position : m = a + (m - a) := by module
  rw [position, det_add_right, at_base, at_copy] at nonpositive
  exact ⟨contact_eq, by linarith⟩

end SixVertexUnfolding.Contact
