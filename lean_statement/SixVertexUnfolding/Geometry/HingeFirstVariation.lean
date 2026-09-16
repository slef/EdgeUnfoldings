import SixVertexUnfolding.Geometry.HingeCoordinates

/-! Moving a crossing along a hinge gives the first-variation equation for
a shortest two-face route. In an outward planar development it forces a
straight crossing. No surface or unfolding theorem is assumed here. -/

namespace SixVertexUnfolding

open Set Filter
open scoped Topology

section Derivative

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Differentiate a nonzero vector's length using the derivative of its squared norm. -/
theorem hasDerivAt_vector_norm {f : ℝ → E} {d : E} {t : ℝ}
    (derivative : HasDerivAt f d t) (nonzero : f t ≠ 0) :
    HasDerivAt (fun r => ‖f r‖) (inner ℝ (f t) d / ‖f t‖) t := by
  have squared := derivative.norm_sq.sqrt (pow_ne_zero 2 (norm_ne_zero_iff.mpr nonzero))
  simpa only [Real.sqrt_sq (norm_nonneg _), mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]
    using squared

/-- At an interior minimum, the two unit directions have cancelling hinge components. -/
theorem hinge_distance_stationary (z x y axis : E) (xz : x ≠ z) (yz : y ≠ z)
    (minimum : IsLocalMin (fun r : ℝ => dist x (r • axis + z) + dist y (r • axis + z)) 0) :
    inner ℝ axis (x - z) / ‖x - z‖ + inner ℝ axis (y - z) / ‖y - z‖ = 0 := by
  have derivative (p : E) (different : p ≠ z) :
      HasDerivAt (fun r : ℝ => dist p (r • axis + z))
        (-(inner ℝ axis (p - z) / ‖p - z‖)) 0 := by
    have vector : HasDerivAt (fun r : ℝ => p - (r • axis + z)) (-axis) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const axis).add_const z |>.const_sub p
    have length := hasDerivAt_vector_norm vector (by simpa using sub_ne_zero.mpr different)
    simpa only [zero_smul, zero_add, inner_neg_right, real_inner_comm (p - z) axis,
      neg_div, dist_eq_norm] using length
  have zero := minimum.hasDerivAt_eq_zero ((derivative x xz).add (derivative y yz))
  linarith

end Derivative

/-- Opposite unit vectors perpendicular to the same planar axis have cancelling remainders. -/
theorem unit_directions_eq_neg_of_hinge_components (axis u v : Plane)
    (axis_unit : ‖axis‖ = 1) (u_unit : ‖u‖ = 1) (v_unit : ‖v‖ = 1)
    (along : inner ℝ axis u + inner ℝ axis v = 0)
    (opposite : inner ℝ (hingeRemainder axis u) (hingeRemainder axis v) ≤ 0) : u = -v := by
  have axis_nonzero : axis ≠ 0 := by intro h; simp [h] at axis_unit
  have u_sq := hingeRemainder_norm_sq axis_unit u
  have v_sq := hingeRemainder_norm_sq axis_unit v
  rw [u_unit] at u_sq
  rw [v_unit] at v_sq
  have along_eq : inner ℝ axis v = -inner ℝ axis u := by linarith
  rw [along_eq, neg_sq] at v_sq
  have remainders : ‖hingeRemainder axis u‖ = ‖hingeRemainder axis v‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    nlinarith
  have perpendicular := opposite_perpendicular_inner axis _ _ axis_nonzero
    (hingeRemainder_orthogonal axis_unit u) (hingeRemainder_orthogonal axis_unit v) opposite
  apply (inner_eq_neg_one_iff_of_norm_eq_one (𝕜 := ℝ) u_unit v_unit).mp
  rw [inner_eq_hinge_components axis_unit, perpendicular, ← remainders]
  rw [along_eq]
  nlinarith

/-- A stationary two-segment route flattens to opposite directions across an outward hinge. -/
theorem stationary_hinge_directions_opposite (axis u v : Plane)
    (axis_unit : ‖axis‖ = 1) (u_nonzero : u ≠ 0) (v_nonzero : v ≠ 0)
    (along : inner ℝ axis u / ‖u‖ + inner ℝ axis v / ‖v‖ = 0)
    (opposite : inner ℝ (hingeRemainder axis u) (hingeRemainder axis v) ≤ 0) :
    NormedSpace.normalize u = -NormedSpace.normalize v := by
  apply unit_directions_eq_neg_of_hinge_components axis _ _ axis_unit
    (NormedSpace.norm_normalize u_nonzero) (NormedSpace.norm_normalize v_nonzero)
  · simpa only [NormedSpace.normalize, inner_smul_right, div_eq_inv_mul] using along
  · have scaled (r : ℝ) (w : Plane) : hingeRemainder axis (r • w) = r • hingeRemainder axis w := by
      simp only [hingeRemainder, inner_smul_right, mul_smul, smul_sub]
    simp only [NormedSpace.normalize, scaled, inner_smul_left, inner_smul_right]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (norm_nonneg _))
      (mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (norm_nonneg _)) opposite)

end SixVertexUnfolding
