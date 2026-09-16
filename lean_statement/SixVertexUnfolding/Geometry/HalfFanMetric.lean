import SixVertexUnfolding.Geometry.TriangleMetricComparison

/-! The metric comparison behind the half-fan lemma, including a right source angle. -/

namespace SixVertexUnfolding.HalfFan

open Real EuclideanGeometry

/-- Increasing the pole distance decreases the viewing angle in the nonobtuse-source branch. -/
theorem cosine_increases {r s D t α γ : ℝ}
    (r_pos : 0 < r) (D_pos : 0 < D) (longer : D ≤ t)
    (nonobtuse : r ^ 2 ≤ s ^ 2 + D ^ 2)
    (original : 2 * r * D * cos α = r ^ 2 + D ^ 2 - s ^ 2)
    (flat : 2 * r * t * cos γ = r ^ 2 + t ^ 2 - s ^ 2) :
    cos α ≤ cos γ := by
  have t_pos : 0 < t := lt_of_lt_of_le D_pos longer
  have factor : 0 ≤ t * D - r ^ 2 + s ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr longer) D_pos.le]
  have identity : (2 * r * t * D) * (cos γ - cos α) =
      (t - D) * (t * D - r ^ 2 + s ^ 2) := by
    linear_combination D * flat - t * original
  have nonnegative := mul_nonneg (sub_nonneg.mpr longer) factor
  have coefficient : 0 < 2 * r * t * D := by positivity
  nlinarith

/-- If the original source angle is obtuse, the developed viewing angle is acute. -/
theorem cosine_positive {r s D t γ : ℝ}
    (r_pos : 0 < r) (t_pos : 0 < t)
    (obtuse : s ^ 2 + D ^ 2 < r ^ 2)
    (flat : 2 * r * t * cos γ = r ^ 2 + t ^ 2 - s ^ 2) :
    0 < cos γ := by
  have numerator : 0 < r ^ 2 + t ^ 2 - s ^ 2 := by nlinarith [sq_nonneg D]
  have coefficient : 0 < 2 * r * t := by positivity
  nlinarith

section Triangles

variable (w v u : Space) (W V U : Plane)
variable (wu : dist W U = dist w u) (vu : dist V U = dist v u)
variable (longer : dist w v ≤ dist W V)

include wu vu longer

/-- For triangles with the same two sides at `u`, a longer pole side narrows the angle at `w`
when the original angle at `v` is nonobtuse. -/
theorem viewing_angle_le (wu_ne : w ≠ u) (wv_ne : w ≠ v)
    (nonobtuse : dist w u ^ 2 ≤ dist v u ^ 2 + dist w v ^ 2) :
    angle U W V ≤ angle u w v := by
  have original := law_cos u w v
  have flat := law_cos U W V
  simp only [dist_comm u w, dist_comm u v, dist_comm v w,
    dist_comm U W, dist_comm U V, dist_comm V W, wu, vu, ← sq] at original flat
  have comparison := cosine_increases (dist_pos.mpr wu_ne) (dist_pos.mpr wv_ne) longer nonobtuse
    (by linarith : 2 * dist w u * dist w v * cos (angle u w v) =
      dist w u ^ 2 + dist w v ^ 2 - dist v u ^ 2)
    (by linarith : 2 * dist w u * dist W V * cos (angle U W V) =
      dist w u ^ 2 + dist W V ^ 2 - dist v u ^ 2)
  exact (strictAntiOn_cos.le_iff_ge ⟨angle_nonneg _ _ _, angle_le_pi _ _ _⟩
    ⟨angle_nonneg _ _ _, angle_le_pi _ _ _⟩).mp comparison

/-- The alternative branch gives an acute viewing angle after development. -/
theorem viewing_angle_acute (wu_ne : w ≠ u) (wv_ne : w ≠ v)
    (obtuse : dist v u ^ 2 + dist w v ^ 2 < dist w u ^ 2) :
    angle U W V < π / 2 := by
  have flat := law_cos U W V
  simp only [dist_comm U W, dist_comm U V, dist_comm V W, wu, vu, ← sq] at flat
  have positive := cosine_positive (dist_pos.mpr wu_ne)
    (lt_of_lt_of_le (dist_pos.mpr wv_ne) longer) obtuse
    (by linarith : 2 * dist w u * dist W V * cos (angle U W V) =
      dist w u ^ 2 + dist W V ^ 2 - dist v u ^ 2)
  have compare : cos (π / 2) < cos (angle U W V) := by simpa using positive
  exact (strictAntiOn_cos.lt_iff_gt ⟨by positivity, by linarith [pi_pos]⟩
    ⟨angle_nonneg _ _ _, angle_le_pi _ _ _⟩).mp compare

end Triangles
end SixVertexUnfolding.HalfFan
