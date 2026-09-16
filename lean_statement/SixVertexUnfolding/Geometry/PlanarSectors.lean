import SixVertexUnfolding.Geometry.PlanarDirections
import SixVertexUnfolding.Geometry.Separation

/-! Two successive angular sectors within one turn have disjoint triangle interiors. -/

namespace SixVertexUnfolding

open Real

/-- A radial triangle occupying the closed angular interval from `α` to `β`. -/
def radialTriangle (r s α β : ℝ) : Set Plane :=
  convexHull ℝ ({0, r • direction α, s • direction β} : Set Plane)

/-- The separating line can be chosen in both angular gaps, including zero-width gaps. -/
theorem sector_separator_angle {α β γ δ : ℝ} (ordered : β ≤ γ)
    (left_width : β - α ≤ π) (right_width : δ - γ ≤ π) (one_turn : δ - α ≤ 2 * π) :
    ∃ θ : ℝ, β ≤ θ ∧ θ ≤ γ ∧ δ - π ≤ θ ∧ θ ≤ α + π := by
  refine ⟨max β (δ - π), le_max_left _ _, ?_, le_max_right _ _, ?_⟩
  · exact max_le ordered (by linarith)
  · exact max_le (by linarith) (by linarith)

/-- All radial triangles in ordered sectors of a single turn are separated by a line through the pole. -/
theorem radial_triangles_disjoint {r s t u α β γ δ : ℝ}
    (r_nonneg : 0 ≤ r) (s_nonneg : 0 ≤ s) (t_nonneg : 0 ≤ t) (u_nonneg : 0 ≤ u)
    (left_order : α ≤ β) (between : β ≤ γ) (right_order : γ ≤ δ)
    (left_width : β - α ≤ π) (right_width : δ - γ ≤ π) (one_turn : δ - α ≤ 2 * π) :
    Disjoint (interior (radialTriangle r s α β)) (interior (radialTriangle t u γ δ)) := by
  obtain ⟨θ, beta_le, le_gamma, delta_le, le_alpha⟩ := sector_separator_angle between left_width right_width one_turn
  have left_ray (x : ℝ) (hx : α ≤ x) (hy : x ≤ β) : det (direction θ) (direction x) ≤ 0 := by
    rw [direction_det]
    exact sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith)
  have right_ray (x : ℝ) (hx : γ ≤ x) (hy : x ≤ δ) : 0 ≤ det (direction θ) (direction x) := by
    rw [direction_det]
    exact sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  apply disjoint_interiors_of_halfplanes (detHeight (direction θ)) (direction_height_surjective θ) 0
  · apply convexHull_min _ ((convex_Iic 0).linear_preimage (detHeight (direction θ)).toLinearMap)
    rintro x (rfl | rfl | rfl)
    · simp [det]
    · change det (direction θ) (r • direction α) ≤ 0
      rw [det_smul_right]
      exact mul_nonpos_of_nonneg_of_nonpos r_nonneg (left_ray α le_rfl left_order)
    · change det (direction θ) (s • direction β) ≤ 0
      rw [det_smul_right]
      exact mul_nonpos_of_nonneg_of_nonpos s_nonneg (left_ray β left_order le_rfl)
  · apply convexHull_min _ ((convex_Ici 0).linear_preimage (detHeight (direction θ)).toLinearMap)
    rintro x (rfl | rfl | rfl)
    · simp [det]
    · change 0 ≤ det (direction θ) (t • direction γ)
      rw [det_smul_right]
      exact mul_nonneg t_nonneg (right_ray γ le_rfl right_order)
    · change 0 ≤ det (direction θ) (u • direction δ)
      rw [det_smul_right]
      exact mul_nonneg u_nonneg (right_ray δ right_order le_rfl)

end SixVertexUnfolding
