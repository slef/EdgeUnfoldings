import SixVertexUnfolding.Geometry.PlanarSectors
import SixVertexUnfolding.Geometry.OutwardPatch

/-! Positive angular gaps separate closed radial triangles away from their common pole. -/

namespace SixVertexUnfolding

open Real

/-- A linear height positive at both outer corners is positive throughout the radial triangle except at zero. -/
theorem radial_hull_height_pos (height : Plane →ₗ[ℝ] ℝ) (a b x : Plane)
    (left : 0 < height a) (right : 0 < height b)
    (member : x ∈ convexHull ℝ ({0, a, b} : Set Plane)) (nonzero : x ≠ 0) : 0 < height x := by
  rw [convexHull_insert (show ({a, b} : Set Plane).Nonempty from ⟨a, by simp⟩)] at member
  obtain ⟨z, hz, y, hy, between⟩ := mem_convexJoin.mp member
  have same : z = 0 := hz
  subst z
  obtain ⟨s, t, hs, ht, total, expression⟩ := between
  simp only [smul_zero, zero_add] at expression
  have positive : 0 < t := by
    apply lt_of_le_of_ne ht
    intro zero
    apply nonzero
    rw [← expression, ← zero, zero_smul]
  have y_positive : 0 < height y := by
    apply convexHull_min _ ((convex_Ioi (0 : ℝ)).linear_preimage height) hy
    rintro p (rfl | rfl)
    exacts [left, right]
  rw [← expression, map_smul, smul_eq_mul]
  exact mul_pos positive y_positive

theorem radial_hull_height_neg (height : Plane →ₗ[ℝ] ℝ) (a b x : Plane)
    (left : height a < 0) (right : height b < 0)
    (member : x ∈ convexHull ℝ ({0, a, b} : Set Plane)) (nonzero : x ≠ 0) : height x < 0 := by
  have positive := radial_hull_height_pos (-height) a b x (by simpa using left) (by simpa using right) member nonzero
  simpa using positive

/-- With a positive gap on both sides, a separator can be chosen strictly inside both gaps. -/
theorem strict_sector_separator {α β γ δ : ℝ} (between : β < γ)
    (left_width : β - α < π) (right_width : δ - γ < π) (one_turn : δ - α < 2 * π) :
    ∃ θ : ℝ, β < θ ∧ θ < γ ∧ δ - π < θ ∧ θ < α + π := by
  have gap : max β (δ - π) < min γ (α + π) :=
    max_lt (lt_min between (by linarith)) (lt_min (by linarith) (by linarith))
  let θ := (max β (δ - π) + min γ (α + π)) / 2
  have lower : max β (δ - π) < θ := by dsimp [θ]; linarith
  have upper : θ < min γ (α + π) := by dsimp [θ]; linarith
  exact ⟨θ, lt_of_le_of_lt (le_max_left _ _) lower,
    lt_of_lt_of_le upper (min_le_left _ _), lt_of_le_of_lt (le_max_right _ _) lower,
    lt_of_lt_of_le upper (min_le_right _ _)⟩

/-- Two closed radial triangles with positive angular gaps can meet only at their common pole. -/
theorem radial_triangles_meet_only_at_zero {r s t u α β γ δ : ℝ}
    (r_pos : 0 < r) (s_pos : 0 < s) (t_pos : 0 < t) (u_pos : 0 < u)
    (left_order : α ≤ β) (between : β < γ) (right_order : γ ≤ δ)
    (left_width : β - α < π) (right_width : δ - γ < π) (one_turn : δ - α < 2 * π)
    (x : Plane) (left : x ∈ radialTriangle r s α β) (right : x ∈ radialTriangle t u γ δ) : x = 0 := by
  by_contra nonzero
  obtain ⟨θ, beta_lt, lt_gamma, delta_lt, lt_alpha⟩ := strict_sector_separator between left_width right_width one_turn
  have left_ray (a : ℝ) (lo : α ≤ a) (hi : a ≤ β) : det (direction θ) (direction a) < 0 := by
    rw [direction_det]
    exact sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)
  have right_ray (a : ℝ) (lo : γ ≤ a) (hi : a ≤ δ) : 0 < det (direction θ) (direction a) := by
    rw [direction_det]
    exact sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have negative : det (direction θ) x < 0 := by
    apply radial_hull_height_neg (detHeight (direction θ)).toLinearMap _ _ x _ _ left nonzero
    · change det (direction θ) (r • direction α) < 0
      rw [det_smul_right]
      exact mul_neg_of_pos_of_neg r_pos (left_ray α le_rfl left_order)
    · change det (direction θ) (s • direction β) < 0
      rw [det_smul_right]
      exact mul_neg_of_pos_of_neg s_pos (left_ray β left_order le_rfl)
  have positive : 0 < det (direction θ) x := by
    apply radial_hull_height_pos (detHeight (direction θ)).toLinearMap _ _ x _ _ right nonzero
    · change 0 < det (direction θ) (t • direction γ)
      rw [det_smul_right]
      exact mul_pos t_pos (right_ray γ le_rfl right_order)
    · change 0 < det (direction θ) (u • direction δ)
      rw [det_smul_right]
      exact mul_pos u_pos (right_ray δ right_order le_rfl)
  linarith

end SixVertexUnfolding
