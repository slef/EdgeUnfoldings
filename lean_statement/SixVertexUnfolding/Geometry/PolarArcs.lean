import SixVertexUnfolding.Geometry.PolarPointUniqueness
import SixVertexUnfolding.Geometry.DirectionIdentities

/-! Small circular arcs around the pole distinguish the two sides of a pocket. -/

namespace SixVertexUnfolding

open Real EuclideanGeometry

/-- The Cartesian unit direction varies continuously with its angle. -/
theorem direction_continuous : Continuous direction := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i
  · exact continuous_cos
  · exact continuous_sin

/-- Every nonzero point has a polar representative within any prescribed full turn. -/
theorem polar_representation_in_turn (α : ℝ) (x : Plane) (nonzero : x ≠ 0) :
    ∃ θ, α ≤ θ ∧ θ ≤ α + 2 * π ∧ x = dist 0 x • direction θ := by
  let φ := angle (direction α) 0 x
  have lo : 0 ≤ φ := angle_nonneg _ _ _
  have hi : φ ≤ π := angle_le_pi _ _ _
  have radius : 0 < dist 0 x := dist_pos.mpr nonzero.symm
  by_cases above : 0 ≤ det (direction α) x
  · refine ⟨α + φ, by linarith, by linarith [pi_pos], ?_⟩
    apply polar_point_eq_of_cos_and_side 1 (dist 0 x) α (α + φ) (by norm_num) radius x rfl
    · simp only [one_smul, add_sub_cancel_left, φ]
    · rw [add_sub_cancel_left]
      exact mul_nonneg above (sin_nonneg_of_nonneg_of_le_pi lo hi)
  · refine ⟨α + 2 * π - φ, by linarith [pi_pos], by linarith, ?_⟩
    apply polar_point_eq_of_cos_and_side 1 (dist 0 x) α (α + 2 * π - φ) (by norm_num) radius x rfl
    · rw [show α + 2 * π - φ - α = -φ + 2 * π by ring, cos_add_two_pi, cos_neg, one_smul]
    · rw [show α + 2 * π - φ - α = -φ + 2 * π by ring, sin_add_two_pi, sin_neg]
      exact mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge above)
        (neg_nonpos.mpr (sin_nonneg_of_nonneg_of_le_pi lo hi))

/-- Positive polar representatives in less than one turn have a unique angle. -/
theorem polar_angle_eq_of_one_turn (r s α β : ℝ) (r_pos : 0 < r) (s_pos : 0 < s)
    (lower : -(2 * π) < β - α) (upper : β - α < 2 * π)
    (same : r • direction α = s • direction β) : α = β := by
  have radii := congrArg (dist (0 : Plane)) same
  rw [polar_radius r α r_pos.le, polar_radius s β s_pos.le] at radii
  subst s
  have distance := polar_distance_sq r r α β
  rw [same, dist_self] at distance
  have cosine : cos (β - α) = 1 := by nlinarith [sq_pos_of_pos r_pos]
  have zero := (cos_eq_one_iff_of_lt_of_lt lower upper).mp cosine
  linarith

/-- An interior angle of an arc cannot meet either of its distinct radial boundary segments. -/
theorem polar_point_not_mem_radial_segment (r R θ φ : ℝ) (positive : 0 < r) (length : 0 ≤ R)
    (lower : -(2 * π) < φ - θ) (upper : φ - θ < 2 * π) (different : θ ≠ φ) :
    r • direction θ ∉ segment ℝ (0 : Plane) (R • direction φ) := by
  rintro ⟨s, t, hs, ht, total, expression⟩
  simp only [smul_zero, zero_add, smul_smul] at expression
  have radii := congrArg (dist (0 : Plane)) expression
  rw [polar_radius (t * R) φ (mul_nonneg ht length), polar_radius r θ positive.le] at radii
  exact different (polar_angle_eq_of_one_turn r (t * R) θ φ positive
    (by linarith) lower upper expression.symm)

/-- Each open circular arc is connected; no polar-coordinate topology is needed. -/
theorem polar_arc_preconnected (r α β : ℝ) :
    IsPreconnected ((fun θ => r • direction θ) '' Set.Ioo α β) :=
  isPreconnected_Ioo.image _ (continuous_const.smul direction_continuous).continuousOn

end SixVertexUnfolding
