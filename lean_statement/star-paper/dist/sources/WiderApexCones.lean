import SixVertexUnfolding.Geometry.ConeHalfplanes
import SixVertexUnfolding.Geometry.BaseConeSeparation

/-! A short cut ray permits an outer apex cone wider than the angle between the two cut rays. -/

namespace SixVertexUnfolding

open Real

/-- The half-sum angle bound is exactly the sine comparison needed by the wider separator. -/
theorem wider_cone_sine_comparison (θ lam : ℝ) (θ_pos : 0 < θ) (beyond : θ < lam)
    (bounded : lam ≤ (π + θ) / 2) : sin (lam - θ) ≤ sin lam := by
  have identity := sin_sub_sin lam (lam - θ)
  have half_pos : 0 ≤ (lam - (lam - θ)) / 2 := by linarith
  have half_small : (lam - (lam - θ)) / 2 ≤ π := by linarith [pi_pos]
  have cosine_nonnegative : 0 ≤ cos ((lam + (lam - θ)) / 2) :=
    cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], by linarith⟩
  have sine_nonnegative := sin_nonneg_of_nonneg_of_le_pi half_pos half_small
  nlinarith [mul_nonneg sine_nonnegative cosine_nonnegative]

/-- With a short left cut side, its outer angle may be as large as half of pi plus the central angle. -/
theorem wider_apex_cones_left (p q : Plane) (δ θ lam rho A B : ℝ)
    (θ_pos : 0 < θ) (θ_small : θ < π)
    (lam_pos : 0 < lam) (lam_small : lam < π) (rho_pos : 0 < rho) (rho_small : rho < π)
    (angle_sum : lam + rho < π + θ) (wide_bound : lam ≤ (π + θ) / 2)
    (left_short : A ≤ 0) (strict_sum : A + B < 0)
    (displacement : q - p = A • direction (δ + θ) + B • direction δ) :
    Disjoint (interior (translatedCone p (direction (δ + θ - lam)) (direction (δ + θ))))
      (interior (translatedCone q (-direction δ) (-direction (δ + rho)))) := by
  by_cases within : lam ≤ θ
  · apply opposed_cones_interiors_disjoint_of_height p q _ _ _ _ (detHeight (direction δ))
      (direction_height_surjective δ)
    · change det (direction δ) (q - p) ≤ 0
      rw [displacement, det_add_right, det_smul_right, det_smul_right, direction_det, direction_det,
        show δ + θ - δ = θ by ring, sub_self, sin_zero, mul_zero, add_zero]
      exact mul_nonpos_of_nonpos_of_nonneg left_short (sin_pos_of_pos_of_lt_pi θ_pos θ_small).le
    · change 0 ≤ det (direction δ) (direction (δ + θ - lam))
      rw [direction_det]
      apply sin_nonneg_of_nonneg_of_le_pi <;> linarith
    · change 0 ≤ det (direction δ) (direction (δ + θ))
      rw [direction_det]
      apply sin_nonneg_of_nonneg_of_le_pi <;> linarith
    · change 0 ≤ det (direction δ) (direction δ)
      rw [det_self]
    · change 0 ≤ det (direction δ) (direction (δ + rho))
      rw [direction_det]
      apply sin_nonneg_of_nonneg_of_le_pi <;> linarith
  · have beyond : θ < lam := lt_of_not_ge within
    let g := direction (δ + θ - lam)
    have difference_pos : 0 < sin (lam - θ) :=
      sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    have sine_order := wider_cone_sine_comparison θ lam θ_pos beyond wide_bound
    have negative_height : det g (q - p) < 0 := by
      rw [displacement, det_add_right, det_smul_right, det_smul_right]
      change A * det (direction (δ + θ - lam)) (direction (δ + θ)) +
        B * det (direction (δ + θ - lam)) (direction δ) < 0
      rw [direction_det, direction_det, show δ + θ - (δ + θ - lam) = lam by ring,
        show δ - (δ + θ - lam) = lam - θ by ring]
      have first := mul_nonpos_of_nonpos_of_nonneg left_short (sub_nonneg.mpr sine_order)
      have second := mul_neg_of_neg_of_pos strict_sum difference_pos
      nlinarith
    have ray_nonnegative (x : ℝ) (lo : δ + θ - lam ≤ x) (hi : x ≤ δ + θ - lam + π) :
        0 ≤ det g (direction x) := by
      change 0 ≤ det (direction (δ + θ - lam)) (direction x)
      rw [direction_det]
      apply sin_nonneg_of_nonneg_of_le_pi <;> linarith
    have separated := opposed_cones_disjoint_of_height p q
      (direction (δ + θ - lam)) (direction (δ + θ)) (direction δ) (direction (δ + rho))
      (detHeight g).toLinearMap negative_height
      (ray_nonnegative (δ + θ - lam) le_rfl (by linarith [pi_pos]))
      (ray_nonnegative (δ + θ) (by linarith) (by linarith))
      (ray_nonnegative δ (by linarith) (by linarith))
      (ray_nonnegative (δ + rho) (by linarith) (by linarith))
    exact separated.mono interior_subset interior_subset

/-- The symmetric short-right-side criterion uses the other outer angle. -/
theorem wider_apex_cones_right (p q : Plane) (δ θ lam rho A B : ℝ)
    (θ_pos : 0 < θ) (θ_small : θ < π)
    (lam_pos : 0 < lam) (lam_small : lam < π) (rho_pos : 0 < rho) (rho_small : rho < π)
    (angle_sum : lam + rho < π + θ) (wide_bound : rho ≤ (π + θ) / 2)
    (right_short : B ≤ 0) (strict_sum : A + B < 0)
    (displacement : q - p = A • direction (δ + θ) + B • direction δ) :
    Disjoint (interior (translatedCone p (direction (δ + θ - lam)) (direction (δ + θ))))
      (interior (translatedCone q (-direction δ) (-direction (δ + rho)))) := by
  have onto (γ : ℝ) : Function.Surjective (-detHeight (direction γ)) := by
    intro r
    obtain ⟨x, hx⟩ := direction_height_surjective γ (-r)
    refine ⟨x, ?_⟩
    change -detHeight (direction γ) x = r
    rw [hx]
    ring
  by_cases within : rho ≤ θ
  · apply opposed_cones_interiors_disjoint_of_height p q _ _ _ _ (-detHeight (direction (δ + θ))) (onto _)
    · change -det (direction (δ + θ)) (q - p) ≤ 0
      rw [displacement, det_add_right, det_smul_right, det_smul_right, det_self, mul_zero, zero_add,
        direction_det, show δ - (δ + θ) = -θ by ring, sin_neg]
      have signed := mul_nonpos_of_nonpos_of_nonneg right_short (sin_pos_of_pos_of_lt_pi θ_pos θ_small).le
      nlinarith
    · change 0 ≤ -det (direction (δ + θ)) (direction (δ + θ - lam))
      rw [det_swap, neg_neg, direction_det]
      apply sin_nonneg_of_nonneg_of_le_pi <;> linarith
    · change 0 ≤ -det (direction (δ + θ)) (direction (δ + θ))
      rw [det_self, neg_zero]
    · change 0 ≤ -det (direction (δ + θ)) (direction δ)
      rw [det_swap, neg_neg, direction_det]
      apply sin_nonneg_of_nonneg_of_le_pi <;> linarith
    · change 0 ≤ -det (direction (δ + θ)) (direction (δ + rho))
      rw [det_swap, neg_neg, direction_det]
      apply sin_nonneg_of_nonneg_of_le_pi <;> linarith
  · have beyond : θ < rho := lt_of_not_ge within
    let g := direction (δ + rho)
    have difference_pos : 0 < sin (rho - θ) :=
      sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    have sine_order := wider_cone_sine_comparison θ rho θ_pos beyond wide_bound
    have negative_height : -det g (q - p) < 0 := by
      rw [displacement, det_add_right, det_smul_right, det_smul_right]
      change -(A * det (direction (δ + rho)) (direction (δ + θ)) +
        B * det (direction (δ + rho)) (direction δ)) < 0
      rw [direction_det, direction_det, show δ + θ - (δ + rho) = -(rho - θ) by ring,
        show δ - (δ + rho) = -rho by ring, sin_neg, sin_neg]
      have first := mul_nonpos_of_nonpos_of_nonneg right_short (sub_nonneg.mpr sine_order)
      have second := mul_neg_of_neg_of_pos strict_sum difference_pos
      nlinarith
    have ray_nonnegative (x : ℝ) (lo : δ + rho - π ≤ x) (hi : x ≤ δ + rho) :
        0 ≤ -det g (direction x) := by
      change 0 ≤ -det (direction (δ + rho)) (direction x)
      rw [det_swap, neg_neg, direction_det]
      apply sin_nonneg_of_nonneg_of_le_pi <;> linarith
    have separated := opposed_cones_disjoint_of_height p q
      (direction (δ + θ - lam)) (direction (δ + θ)) (direction δ) (direction (δ + rho))
      (-detHeight g).toLinearMap negative_height
      (ray_nonnegative (δ + θ - lam) (by linarith) (by linarith))
      (ray_nonnegative (δ + θ) (by linarith) (by linarith))
      (ray_nonnegative δ (by linarith) (by linarith))
      (ray_nonnegative (δ + rho) (by linarith [pi_pos]) le_rfl)
    exact separated.mono interior_subset interior_subset

/-- If both outer angles satisfy the wider bound, the strict distance sum guarantees a short side. -/
theorem wider_apex_cones (p q : Plane) (δ θ lam rho A B : ℝ)
    (θ_pos : 0 < θ) (θ_small : θ < π)
    (lam_pos : 0 < lam) (lam_small : lam < π) (rho_pos : 0 < rho) (rho_small : rho < π)
    (angle_sum : lam + rho < π + θ)
    (left_bound : lam ≤ (π + θ) / 2) (right_bound : rho ≤ (π + θ) / 2)
    (strict_sum : A + B < 0)
    (displacement : q - p = A • direction (δ + θ) + B • direction δ) :
    Disjoint (interior (translatedCone p (direction (δ + θ - lam)) (direction (δ + θ))))
      (interior (translatedCone q (-direction δ) (-direction (δ + rho)))) := by
  by_cases left_short : A ≤ 0
  · exact wider_apex_cones_left p q δ θ lam rho A B θ_pos θ_small lam_pos lam_small rho_pos rho_small
      angle_sum left_bound left_short strict_sum displacement
  · exact wider_apex_cones_right p q δ θ lam rho A B θ_pos θ_small lam_pos lam_small rho_pos rho_small
      angle_sum right_bound (by linarith) strict_sum displacement

end SixVertexUnfolding
