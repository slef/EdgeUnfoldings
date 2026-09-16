import SixVertexUnfolding.Geometry.ContactSineBudget
import SixVertexUnfolding.Geometry.TriangleHalfplanes

/-! Determinants turn actual finite contact and triangle containment into the two sine inequalities. -/

namespace SixVertexUnfolding.Contact

open Real

theorem radial_segment_det_zero (Γ R : ℝ) (q : Plane)
    (contact : q ∈ segment ℝ 0 (R • direction Γ)) : det (direction Γ) q = 0 := by
  obtain ⟨u, v, _, _, _, position⟩ := contact
  rw [← position]
  simp only [smul_zero, zero_add, det_smul_right, det_self, mul_zero]

/-- The first equality records finite-slit contact; the inequality records the neighboring apex's containment. -/
theorem polar_contact_sine_data (a m p : Plane) (r s R ω Γ δ θ gap t : ℝ)
    (r_nonnegative : 0 ≤ r) (sine_nonnegative : 0 ≤ sin δ)
    (turn : Γ + δ = ω + 2 * π)
    (at_a : a = r • direction ω)
    (at_m : m - a = s • direction (ω - π + θ))
    (at_p : p - a = s • direction (ω - π + θ + gap))
    (contact : a + t • (p - a) ∈ segment ℝ 0 (R • direction Γ))
    (contained : m ∈ convexHull ℝ ({a, 0, a + t • (p - a)} : Set Plane)) :
    r * sin δ = t * s * sin (θ + gap + δ) ∧
      s * sin (θ + δ) ≤ r * sin δ := by
  have at_base : det (direction Γ) a = r * sin δ := by
    rw [at_a, det_smul_right, direction_det,
      show ω - Γ = δ - 2 * π by linarith, sin_sub_two_pi]
  have at_copy : det (direction Γ) (m - a) = -(s * sin (θ + δ)) := by
    rw [at_m, det_smul_right, direction_det,
      show ω - π + θ - Γ = (θ + δ - π) - 2 * π by linarith,
      sin_sub_two_pi, sin_sub_pi]
    ring
  have at_cut : det (direction Γ) (p - a) = -(s * sin (θ + gap + δ)) := by
    rw [at_p, det_smul_right, direction_det,
      show ω - π + θ + gap - Γ = (θ + gap + δ - π) - 2 * π by linarith,
      sin_sub_two_pi, sin_sub_pi]
    ring
  have on_line := radial_segment_det_zero Γ R _ contact
  have contact_eq : r * sin δ = t * s * sin (θ + gap + δ) := by
    rw [det_add_right, det_smul_right, at_base, at_cut] at on_line
    nlinarith
  have nonnegative : 0 ≤ det (direction Γ) m := by
    let height := detHeight (direction Γ)
    have inclusion : convexHull ℝ ({a, 0, a + t • (p - a)} : Set Plane) ⊆ {x | 0 ≤ height x} := by
      apply convexHull_min _ ((convex_Ici (0 : ℝ)).linear_preimage height.toLinearMap)
      rintro x (rfl | rfl | rfl)
      · change 0 ≤ det (direction Γ) _
        rw [at_base]
        exact mul_nonneg r_nonnegative sine_nonnegative
      · change 0 ≤ det (direction Γ) 0
        simp [det]
      · change 0 ≤ det (direction Γ) (a + t • (p - a))
        exact on_line.ge
    exact inclusion contained
  have position : m = a + (m - a) := by module
  rw [position, det_add_right, at_base, at_copy] at nonnegative
  exact ⟨contact_eq, by linarith⟩

end SixVertexUnfolding.Contact
