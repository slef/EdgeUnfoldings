import SixVertexUnfolding.Geometry.WedgeGapFrame
import SixVertexUnfolding.Geometry.WedgeStep

/-! The complete wedge step in the original junction coordinates.
The circular gap order supplies the arm rotation. The remaining numerical
premise is the outer-angle budget, which the global proof must establish.
-/

namespace SixVertexUnfolding.Wedge

open Real Set EuclideanGeometry

/-- The two radial triangles over one bisecting cut ray, in the junction plane. -/
def gapKite (z : Plane) (d L γ δ : ℝ) : Set Plane :=
  convexHull ℝ ({z, z + L • direction ((γ + δ) / 2), z + d • direction δ} : Set Plane) ∪
  convexHull ℝ ({z + L • direction ((γ + δ) / 2), z, z + d • direction γ} : Set Plane)

private theorem rooted_polar_image (z c : Plane) (turn : Plane ≃ₗᵢ[ℝ] Plane)
    (frame : Plane ≃ᵃⁱ[ℝ] Plane) (formula : ∀ x, frame x = turn (x - z) + c)
    (τ : ℝ) (directions : ∀ φ, turn (direction φ) = direction (φ - τ))
    (d ω lower upper : ℝ) :
    frame '' {x | x - z ∈ polarRegion d ω lower upper} =
      {x | x - c ∈ polarRegion d ω (lower - τ) (upper - τ)} := by
  rw [translated_region_image z c turn frame formula]
  have shifted := polarRegion_image_rotation turn (-τ)
    (fun φ => by simpa only [sub_eq_add_neg] using directions φ) d ω lower upper
  simpa only [← sub_eq_add_neg] using congrArg (fun S : Set Plane => {x | x - c ∈ S}) shifted

/-- Expanding around an outgoing kite gives containment, nonoverlap before
addition, and an exact updated wedge at the next tree vertex. -/
theorem gap_rotate_and_move_with_sources (z : Plane) {d L α β γ δ ω : ℝ}
    (source_positive : 0 < d) (length_positive : 0 < L)
    (gap_ordered : γ < δ) (gap_width : δ < γ + 2 * π)
    (separated : (β ≤ γ ∧ δ ≤ α + 2 * π) ∨ (δ ≤ α ∧ β ≤ γ + 2 * π))
    (outer_lower : π / 2 ≤ ω)
    (budget : ω + angle z (z + d • direction δ) (z + L • direction ((γ + δ) / 2)) ≤ 3 * π / 2) :
    let y := z + L • direction ((γ + δ) / 2)
    let apex := angle z (z + d • direction δ) y
    let W := {x | x - z ∈ polarRegion d ω α β}
    let V := {x | x - z ∈ polarRegion d ω δ (γ + 2 * π)}
    ∃ D Θ : ℝ, 0 < D ∧ 0 < Θ ∧ Θ < π ∧
      z + d • direction δ = y + D • direction (Θ + (γ + δ) / 2) ∧
      z + d • direction γ = y + D • direction (2 * π - Θ + (γ + δ) / 2) ∧
      let W' := {x | x - y ∈ polarRegion D (ω + apex)
        (Θ + (γ + δ) / 2) (2 * π - Θ + (γ + δ) / 2)}
      W ⊆ V ∧ Disjoint V (interior (gapKite z d L γ δ)) ∧ W' = V ∪ gapKite z d L γ δ := by
  dsimp only
  let θ := (δ - γ) / 2
  let h := d * sin θ
  let r := -d * cos θ
  let y := z + L • direction ((γ + δ) / 2)
  let apex := angle z (z + d • direction δ) y
  have outer_upper : ω ≤ 3 * π / 2 := by
    linarith [angle_nonneg z (z + d • direction δ) y]
  obtain ⟨turn, directions, lower, upper, lower_moves, upper_moves, rotated⟩ :=
    rotate_from_disjoint_gap d ω α β γ δ separated
  obtain ⟨height_positive, _, _, frame, formula, at_root, at_lower, at_upper, on_ray⟩ :=
    gap_frame z source_positive gap_ordered gap_width turn directions
  have C := gap_arm_coordinates source_positive gap_ordered gap_width outer_lower outer_upper
  change ArmCoordinates h r _ _ d θ ω at C
  obtain ⟨D, Θ, N⟩ := exists_arm_coordinates (r := r + L) height_positive outer_lower outer_upper
  have angle_eq : angle (point r 0) (point 0 h) (point (r + L) 0) = apex := by
    have preserved := frame.toAffineIsometry.angle_map z (z + d • direction δ) y
    change angle (frame z) (frame (z + d • direction δ)) (frame y) = apex at preserved
    rw [at_root, at_upper, on_ray L] at preserved
    exact preserved
  have step := C.rotate_and_move (q := r + L) (by linarith) N.radius_pos N.angle_pos N.angle_lt_pi
    N.source_x N.source_y lower_moves upper_moves (by rw [angle_eq]; exact budget)
  dsimp only at step
  rw [angle_eq] at step
  have old_image : frame '' {x | x - z ∈ polarRegion d ω α β} =
      {x | x - point r 0 ∈ polarRegion d ω lower upper} := by
    rw [translated_region_image z (point r 0) turn frame formula, rotated]
  have before_image : frame '' {x | x - z ∈ polarRegion d ω δ (γ + 2 * π)} =
      {x | x - point r 0 ∈ polarRegion d ω θ (2 * π - θ)} := by
    rw [rooted_polar_image z (point r 0) turn frame formula ((γ + δ) / 2) directions]
    rw [show δ - (γ + δ) / 2 = θ by dsimp [θ]; ring,
      show γ + 2 * π - (γ + δ) / 2 = 2 * π - θ by dsimp [θ]; ring]
  have next_formula (x : Plane) : frame x = turn (x - y) + point (r + L) 0 := by
    calc
      frame x = turn (x - z) + point r 0 := formula x
      _ = turn ((x - y) + (y - z)) + point r 0 := by rw [sub_add_sub_cancel]
      _ = turn (x - y) + (turn (y - z) + point r 0) := by rw [map_add, add_assoc]
      _ = turn (x - y) + frame y := by rw [formula y]
      _ = turn (x - y) + point (r + L) 0 := by rw [on_ray L]
  have after_image : frame '' {x | x - y ∈ polarRegion D (ω + apex)
        (Θ + (γ + δ) / 2) (2 * π - Θ + (γ + δ) / 2)} =
      {x | x - point (r + L) 0 ∈ polarRegion D (ω + apex) Θ (2 * π - Θ)} := by
    rw [rooted_polar_image y (point (r + L) 0) turn frame next_formula ((γ + δ) / 2) directions,
      add_sub_cancel_right, add_sub_cancel_right]
  have kite_image : frame '' gapKite z d L γ δ = kite h r (r + L) := by
    rw [gapKite, image_union, kite_eq_triangles height_positive (by linarith : r < r + L)]
    have triangle (x y z : Plane) : frame '' convexHull ℝ ({x, y, z} : Set Plane) =
        convexHull ℝ ({frame x, frame y, frame z} : Set Plane) := by
      change frame.toAffineMap '' _ = _
      rw [frame.toAffineMap.image_convexHull]
      simp only [image_insert_eq, image_singleton]
      rfl
    rw [triangle, triangle, at_root, at_upper, at_lower, on_ray L]
  have upper_source : z + d • direction δ = y + D • direction (Θ + (γ + δ) / 2) := by
    apply frame.injective
    rw [at_upper, next_formula, add_sub_cancel_left, map_smul, directions, add_sub_cancel_right]
    ext i
    fin_cases i
    · change 0 = D * cos Θ + (r + L)
      linarith [N.source_x]
    · change d * sin ((δ - γ) / 2) = D * sin Θ + 0
      linarith [N.source_y]
  have lower_source : z + d • direction γ = y + D • direction (2 * π - Θ + (γ + δ) / 2) := by
    apply frame.injective
    rw [at_lower, next_formula, add_sub_cancel_left, map_smul, directions, add_sub_cancel_right,
      direction_two_pi_sub]
    ext i
    fin_cases i
    · change 0 = D * cos (-Θ) + (r + L)
      rw [cos_neg]
      linarith [N.source_x]
    · change -(d * sin ((δ - γ) / 2)) = D * sin (-Θ) + 0
      rw [sin_neg]
      linarith [N.source_y]
  refine ⟨D, Θ, N.radius_pos, N.angle_pos, N.angle_lt_pi, upper_source, lower_source, ?_, ?_, ?_⟩
  · intro x member
    have image_member : frame x ∈ frame '' {x | x - z ∈ polarRegion d ω δ (γ + 2 * π)} := by
      rw [before_image]
      apply step.1
      rw [← old_image]
      exact ⟨x, member, rfl⟩
    obtain ⟨x', hx', same⟩ := image_member
    exact frame.injective same ▸ hx'
  · apply Disjoint.of_image (f := frame)
    have interior_image : frame '' interior (gapKite z d L γ δ) =
        interior (frame '' gapKite z d L γ δ) := frame.toHomeomorph.image_interior _
    rw [before_image, interior_image, kite_image]
    exact step.2.1
  · apply Set.image_injective.mpr frame.injective
    rw [after_image, image_union, before_image, kite_image]
    exact step.2.2

/-- The set-theoretic step, with the source-coordinate identities omitted. -/
theorem gap_rotate_and_move (z : Plane) {d L α β γ δ ω : ℝ}
    (source_positive : 0 < d) (length_positive : 0 < L)
    (gap_ordered : γ < δ) (gap_width : δ < γ + 2 * π)
    (separated : (β ≤ γ ∧ δ ≤ α + 2 * π) ∨ (δ ≤ α ∧ β ≤ γ + 2 * π))
    (outer_lower : π / 2 ≤ ω)
    (budget : ω + angle z (z + d • direction δ) (z + L • direction ((γ + δ) / 2)) ≤ 3 * π / 2) :
    let y := z + L • direction ((γ + δ) / 2)
    let apex := angle z (z + d • direction δ) y
    let W := {x | x - z ∈ polarRegion d ω α β}
    let V := {x | x - z ∈ polarRegion d ω δ (γ + 2 * π)}
    ∃ D Θ : ℝ, 0 < D ∧ 0 < Θ ∧ Θ < π ∧
      let W' := {x | x - y ∈ polarRegion D (ω + apex)
        (Θ + (γ + δ) / 2) (2 * π - Θ + (γ + δ) / 2)}
      W ⊆ V ∧ Disjoint V (interior (gapKite z d L γ δ)) ∧ W' = V ∪ gapKite z d L γ δ := by
  obtain ⟨D, Θ, dp, tp, ts, _, _, step⟩ := gap_rotate_and_move_with_sources z
    source_positive length_positive gap_ordered gap_width separated outer_lower budget
  exact ⟨D, Θ, dp, tp, ts, step⟩

end SixVertexUnfolding.Wedge
