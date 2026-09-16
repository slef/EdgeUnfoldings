import SixVertexUnfolding.Geometry.CenteredWedgeGeometry
import SixVertexUnfolding.Geometry.WedgeGapFrame

/-! A root and a positive point on the symmetry axis determine how a
centered wedge transforms under any rigid change of planar coordinates. -/

namespace SixVertexUnfolding.Wedge

open Set

/-- An affine motion acts about a prescribed root by its linear part. -/
theorem motion_about_root (motion : Plane ≃ᵃⁱ[ℝ] Plane) (z Z : Plane)
    (root : motion z = Z) (x : Plane) :
    motion x = motion.linearIsometryEquiv (x - z) + Z := by
  have difference := motion.map_vsub x z
  change motion.linearIsometryEquiv (x - z) = motion x - motion z at difference
  rw [root] at difference
  exact (eq_sub_iff_add_eq.mp difference).symm

/-- One positive point on the axis identifies the direction of the linear part. -/
theorem motion_axis_direction (motion : Plane ≃ᵃⁱ[ℝ] Plane) (z Z : Plane)
    {L axis other : ℝ} (positive : 0 < L) (root : motion z = Z)
    (on_axis : motion (z + L • direction axis) = Z + L • direction other) :
    motion.linearIsometryEquiv (direction axis) = direction other := by
  rw [motion_about_root motion z Z root, add_sub_cancel_left, map_smul] at on_axis
  have scaled : L • motion.linearIsometryEquiv (direction axis) = L • direction other := by
    rw [add_comm Z (L • direction other)] at on_axis
    exact add_right_cancel on_axis
  exact (smul_right_injective _ positive.ne') scaled

/-- A rooted centered wedge transforms exactly, without choosing an orientation sign. -/
theorem centered_wedge_image (motion : Plane ≃ᵃⁱ[ℝ] Plane) (z Z : Plane)
    {L axis other : ℝ} (positive : 0 < L) (root : motion z = Z)
    (on_axis : motion (z + L • direction axis) = Z + L • direction other)
    (d ω half : ℝ) :
    motion '' {x | x - z ∈ polarRegion d ω (axis - half) (axis + half)} =
      {x | x - Z ∈ polarRegion d ω (other - half) (other + half)} := by
  rw [translated_region_image z Z motion.linearIsometryEquiv motion
    (motion_about_root motion z Z root)]
  rw [centered_polarRegion_image motion.linearIsometryEquiv axis other
    (motion_axis_direction motion z Z positive root on_axis)]

end SixVertexUnfolding.Wedge
