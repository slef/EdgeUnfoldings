import SixVertexUnfolding.Geometry.WedgeCircleSigns
import SixVertexUnfolding.Geometry.PolarArcs

/-! The Cartesian and polar wedges are the same subset of the actual plane.
This connects arm rotation to the root-moving and kite-exclusion lemmas.
-/

namespace SixVertexUnfolding.Wedge

open Real Set

private noncomputable def foldedAngle (ψ : ℝ) : ℝ := min ψ (2 * π - ψ)

private theorem folded_bounds {ψ : ℝ} (turn : ψ ∈ Icc 0 (2 * π)) :
    foldedAngle ψ ∈ Icc 0 π := by
  refine ⟨le_min turn.1 (sub_nonneg.mpr turn.2), ?_⟩
  by_cases first : ψ ≤ π
  · exact (min_le_left _ _).trans first
  · exact (min_le_right _ _).trans (by linarith)

private theorem cos_folded (ψ : ℝ) : cos (foldedAngle ψ) = cos ψ := by
  unfold foldedAngle
  by_cases first : ψ ≤ π
  · rw [min_eq_left (by linarith)]
  · rw [min_eq_right (by linarith)]
    simp [cos_sub]

private theorem sin_folded {ψ : ℝ} (turn : ψ ∈ Icc 0 (2 * π)) :
    sin (foldedAngle ψ) = |sin ψ| := by
  have bounds := folded_bounds turn
  have positive := sin_nonneg_of_nonneg_of_le_pi bounds.1 bounds.2
  have square := cos_sq_add_sin_sq (foldedAngle ψ)
  rw [cos_folded] at square
  nlinarith [cos_sq_add_sin_sq ψ, sq_abs (sin ψ), abs_nonneg (sin ψ)]

/-- Polar membership depends only on the folded angle in the upper semicircle. -/
private theorem polar_membership_on_turn {d γ θ ρ ψ : ℝ}
    (rp : 0 < ρ) (turn : ψ ∈ Icc 0 (2 * π)) :
    ρ • direction ψ ∈ polarRegion d γ θ (2 * π - θ) ↔
      θ + offset d γ ρ ≤ foldedAngle ψ := by
  constructor
  · rintro (zero | ⟨s, δ, sp, position, left, right⟩)
    · have radius := congrArg (dist (0 : Plane)) zero
      rw [polar_radius ρ ψ rp.le, dist_self] at radius
      linarith
    · have radii := congrArg (dist (0 : Plane)) position
      rw [polar_radius ρ ψ rp.le, polar_radius s δ sp.le] at radii
      subst s
      by_cases all : θ + offset d γ ρ ≤ 0
      · exact all.trans (folded_bounds turn).1
      · have beta : 0 < θ + offset d γ ρ := lt_of_not_ge all
        have dt : δ ∈ Icc 0 (2 * π) := ⟨by linarith, by linarith⟩
        have coordinate := congrArg (fun z : Plane => z 0) position
        simp only [PiLp.smul_apply, direction_x, smul_eq_mul] at coordinate
        have cosine : cos ψ = cos δ := by nlinarith
        have folded : foldedAngle ψ = foldedAngle δ :=
          strictAntiOn_cos.injOn (folded_bounds turn) (folded_bounds dt)
            (by simpa only [cos_folded] using cosine)
        rw [folded]
        exact le_min left (by linarith)
  · intro member
    refine Or.inr ⟨ρ, ψ, rp, rfl, member.trans (min_le_left _ _), ?_⟩
    have other := member.trans (min_le_right _ _)
    linarith

namespace ArmCoordinates

variable {h r a b d θ γ : ℝ} (C : ArmCoordinates h r a b d θ γ)
include C

/-- The desired identity, including the root, boundary rays, and all wedge shapes. -/
theorem mem_region_iff_polar (z : Plane) :
    z ∈ region h r a b ↔ z - point r 0 ∈ polarRegion d γ θ (2 * π - θ) := by
  by_cases at_root : z - point r 0 = 0
  · have same : z = point r 0 := sub_eq_zero.mp at_root
    rw [same, sub_self]
    constructor
    · exact fun _ => Or.inl rfl
    · intro _
      apply (mem_region_iff_level C.height_pos C.outward C.ray_nonzero _).mpr
      have zero := level_zero_of_inner C.height_pos C.outward C.height_pos.le
        (show h * r = r * (h - 0) by ring)
      simpa [point] using zero.le
  · obtain ⟨ψ, low, high, representation⟩ := polar_representation_in_turn 0 (z - point r 0) at_root
    let ρ := dist 0 (z - point r 0)
    have rp : 0 < ρ := dist_pos.mpr (Ne.symm at_root)
    have turn : ψ ∈ Icc 0 (2 * π) := ⟨low, by simpa using high⟩
    have px := congrArg (fun p : Plane => p 0) representation
    have py := congrArg (fun p : Plane => p 1) representation
    change z 0 - r = ρ * cos ψ at px
    change z 1 - 0 = ρ * sin ψ at py
    have xeq : z 0 = r + ρ * cos ψ := by linarith
    have yeq : |z 1| = ρ * sin (foldedAngle ψ) := by
      rw [show z 1 = ρ * sin ψ by linarith, abs_mul, abs_of_pos rp, sin_folded turn]
    rw [mem_region_iff_level C.height_pos C.outward C.ray_nonzero, representation,
      polar_membership_on_turn rp turn, xeq, yeq, ← cos_folded ψ]
    exact C.circle_sign rp (folded_bounds turn)

end ArmCoordinates

/-- The outer-ray formulas used in the original Cartesian definition produce
exactly the same region as the angular construction. -/
theorem cartesian_polar_bridge {h r d θ γ : ℝ}
    (dp : 0 < d) (theta_pos : 0 < θ) (theta_lt_pi : θ < π)
    (source_x : -r = d * cos θ) (source_y : h = d * sin θ)
    (lower : π / 2 ≤ γ) (upper : γ ≤ 3 * π / 2) (z : Plane) :
    z ∈ region h r (r * cos γ - h * sin γ) (-r * sin γ - h * cos γ) ↔
      z - point r 0 ∈ polarRegion d γ θ (2 * π - θ) := by
  apply ArmCoordinates.mem_region_iff_polar
  refine ⟨dp, theta_pos, theta_lt_pi, lower, upper, source_x, source_y, ?_, ?_⟩
  · simp only [cos_add, cos_pi_sub, sin_pi_sub]
    rw [source_y, show r = -(d * cos θ) by linarith]
    ring
  · simp only [sin_add, cos_pi_sub, sin_pi_sub]
    rw [source_y, show r = -(d * cos θ) by linarith]
    ring

/-- Every positive source-image height admits the polar coordinates required
by the bridge; no existence of a coordinate frame is assumed. -/
theorem exists_arm_coordinates {h r γ : ℝ} (hp : 0 < h)
    (lower : π / 2 ≤ γ) (upper : γ ≤ 3 * π / 2) :
    ∃ d θ : ℝ, ArmCoordinates h r (r * cos γ - h * sin γ)
      (-r * sin γ - h * cos γ) d θ γ := by
  have nonzero : point (-r) h ≠ 0 := by
    intro zero
    have coord := congrArg (fun z : Plane => z 1) zero
    have bad : h = 0 := by simpa [point] using coord
    linarith
  let d := dist 0 (point (-r) h)
  have dp : 0 < d := dist_pos.mpr nonzero.symm
  obtain ⟨θ, low, high, position⟩ := polar_representation_in_turn 0 (point (-r) h) nonzero
  have sx := congrArg (fun z : Plane => z 0) position
  have sy := congrArg (fun z : Plane => z 1) position
  change -r = d * cos θ at sx
  change h = d * sin θ at sy
  have sine : 0 < sin θ := by nlinarith
  have theta_pos : 0 < θ := by
    apply lt_of_le_of_ne low
    intro zero
    rw [← zero, sin_zero] at sine
    linarith
  have theta_lt_pi : θ < π := by
    by_contra after
    have negative := sin_nonpos_of_nonpos_of_neg_pi_le
      (show θ - 2 * π ≤ 0 by linarith) (show -π ≤ θ - 2 * π by linarith)
    rw [sin_sub_two_pi] at negative
    linarith
  refine ⟨d, θ, dp, theta_pos, theta_lt_pi, lower, upper, sx, sy, ?_, ?_⟩
  · simp only [cos_add, cos_pi_sub, sin_pi_sub]
    rw [sy, show r = -(d * cos θ) by linarith]
    ring
  · simp only [sin_add, cos_pi_sub, sin_pi_sub]
    rw [sy, show r = -(d * cos θ) by linarith]
    ring

end SixVertexUnfolding.Wedge
