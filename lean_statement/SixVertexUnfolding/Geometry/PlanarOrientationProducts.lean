import SixVertexUnfolding.Geometry.PlaneOrientation

/-! A common rigid frame preserves the product of two signed areas,
including when the frame reverses orientation. -/

namespace SixVertexUnfolding

theorem affine_det_product (motion : Plane ≃ᵃⁱ[ℝ] Plane) (p l r q u v : Plane) :
    det (motion p - motion l) (motion r - motion l) *
      det (motion q - motion u) (motion v - motion u) =
    det (p - l) (r - l) * det (q - u) (v - u) := by
  let linear := motion.linearIsometryEquiv
  have difference (x y : Plane) : motion x - motion y = linear (x - y) :=
    (motion.map_vsub x y).symm
  simp only [difference]
  change det (linear.toLinearMap (p - l)) (linear.toLinearMap (r - l)) *
    det (linear.toLinearMap (q - u)) (linear.toLinearMap (v - u)) = _
  rw [det_linear_map linear.toLinearMap (p - l) (r - l),
    det_linear_map linear.toLinearMap (q - u) (v - u)]
  rw [mul_mul_mul_comm, ← pow_two]
  change det (linear (direction 0)) (linear (direction (Real.pi / 2))) ^ 2 *
    (det (p - l) (r - l) * det (q - u) (v - u)) = _
  rw [isometry_orientation_sq linear, one_mul]

end SixVertexUnfolding
