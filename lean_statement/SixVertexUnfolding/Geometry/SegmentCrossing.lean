import SixVertexUnfolding.Geometry.PlaneOrientation

/-! Signed-side tests give an explicit intersection of two closed planar segments. -/

namespace SixVertexUnfolding

/-- One strict crossing and the two weak reverse-side bounds locate a common segment point. -/
theorem closed_segments_meet_of_sides (a b c d : Plane)
    (c_side : det (b - a) (c - a) < 0)
    (d_side : 0 < det (b - a) (d - a))
    (a_side : 0 ≤ det (d - c) (a - c))
    (b_side : det (d - c) (b - c) ≤ 0) :
    (segment ℝ a b ∩ segment ℝ c d).Nonempty := by
  let α := det (b - a) (c - a)
  let β := det (b - a) (d - a)
  let γ := det (d - c) (a - c)
  let δ := det (d - c) (b - c)
  let denominator := β - α
  have positive : 0 < denominator := sub_pos.mpr (lt_trans c_side d_side)
  have nonzero := ne_of_gt positive
  have difference : γ - δ = denominator := by
    dsimp [γ, δ, denominator, α, β]
    simp only [det, PiLp.sub_apply]
    ring
  let u := γ / denominator
  let t := -α / denominator
  have u_nonneg : 0 ≤ u := div_nonneg a_side positive.le
  have u_le : u ≤ 1 := (div_le_one positive).mpr (by linarith)
  have t_nonneg : 0 ≤ t := div_nonneg (neg_nonneg.mpr c_side.le) positive.le
  have t_le : t ≤ 1 := (div_le_one positive).mpr (by dsimp [denominator]; linarith)
  refine ⟨(1 - u) • a + u • b, ⟨1 - u, u, sub_nonneg.mpr u_le, u_nonneg, by ring, rfl⟩, ?_⟩
  refine ⟨1 - t, t, sub_nonneg.mpr t_le, t_nonneg, by ring, ?_⟩
  dsimp [u, t]
  ext i
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  field_simp
  fin_cases i <;> dsimp [denominator, α, β, γ] <;>
    simp only [det, PiLp.sub_apply] <;> ring

end SixVertexUnfolding
