import SixVertexUnfolding.Definitions

/-!
A five-point affine dependence controls the distances changed by a development.
Positive pole weights and negative equator weights make the missing pole-to-source
distance increase once the pole distance and the other equator distance increase.
-/

namespace SixVertexUnfolding

/-- The squared-distance identity for two pole weights and three equator weights. -/
theorem radon_distance_identity {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b s u v : ℝ) (A B S U V : E) (total : a + b = s + u + v) :
    a * b * dist A B ^ 2 - a * s * dist A S ^ 2 - a * u * dist A U ^ 2 - a * v * dist A V ^ 2 -
      b * s * dist B S ^ 2 - b * u * dist B U ^ 2 - b * v * dist B V ^ 2 +
      s * u * dist S U ^ 2 + s * v * dist S V ^ 2 + u * v * dist U V ^ 2 =
        -‖a • A + b • B - s • S - u • U - v • V‖ ^ 2 := by
  have last_weight : v = a + b - s - u := by linarith
  rw [last_weight]
  simp only [dist_eq_norm, ← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
    inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  simp only [real_inner_comm]
  ring

/-- Two already-increased distances force the missing pole-to-source distance to increase. -/
theorem radon_missing_distance_gt (a b s u v : ℝ) (A B S U V : Space) (A' B' S' U' V' : Plane)
    (a_pos : 0 < a) (b_pos : 0 < b) (s_pos : 0 < s) (v_nonnegative : 0 ≤ v)
    (total : a + b = s + u + v)
    (balance : a • A + b • B = s • S + u • U + v • V)
    (AU : dist A' U' = dist A U) (AV : dist A' V' = dist A V)
    (BU : dist B' U' = dist B U) (BV : dist B' V' = dist B V)
    (UV : dist U' V' = dist U V) (BS : dist B' S' = dist B S) (SU : dist S' U' = dist S U)
    (poles_farther : dist A B < dist A' B') (equator_farther : dist S V ≤ dist S' V') :
    dist A S < dist A' S' := by
  have zero : a • A + b • B - s • S - u • U - v • V = 0 := by rw [balance]; module
  have original := radon_distance_identity a b s u v A B S U V total
  rw [zero, norm_zero, zero_pow (by decide), neg_zero] at original
  have planar := radon_distance_identity a b s u v A' B' S' U' V' total
  rw [AU, AV, BU, BV, UV, BS, SU] at planar
  have pole_sq : dist A B ^ 2 < dist A' B' ^ 2 := (sq_lt_sq₀ dist_nonneg dist_nonneg).mpr poles_farther
  have equator_sq : dist S V ^ 2 ≤ dist S' V' ^ 2 := (sq_le_sq₀ dist_nonneg dist_nonneg).mpr equator_farther
  have pole_gain := mul_pos (mul_pos a_pos b_pos) (sub_pos.mpr pole_sq)
  have equator_gain := mul_nonneg (mul_nonneg s_pos.le v_nonnegative) (sub_nonneg.mpr equator_sq)
  have error_nonnegative := sq_nonneg ‖a • A' + b • B' - s • S' - u • U' - v • V'‖
  have source_gain : 0 < a * s * (dist A' S' ^ 2 - dist A S ^ 2) := by
    nlinarith only [original, planar, pole_gain, equator_gain, error_nonnegative]
  have source_sq : dist A S ^ 2 < dist A' S' ^ 2 := by
    exact sub_pos.mp ((mul_pos_iff_of_pos_left (mul_pos a_pos s_pos)).mp source_gain)
  exact (sq_lt_sq₀ dist_nonneg dist_nonneg).mp source_sq

end SixVertexUnfolding
