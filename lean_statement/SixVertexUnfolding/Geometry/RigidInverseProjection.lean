import SixVertexUnfolding.Geometry.FiniteRigidPieces
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! A rigid plane embedded in space has a nonexpanding inverse
extension: translate to its origin and apply the adjoint projection. -/

namespace SixVertexUnfolding

/-- Orthogonal projection extends the inverse of a rigid affine plane embedding. -/
theorem rigid_plane_inverse_extension (fold : Plane →ᵃ[ℝ] Space) (rigid : Isometry fold) :
    ∃ inverse : Space → Plane, LipschitzWith 1 inverse ∧ ∀ x : Plane, inverse (fold x) = x := by
  let linear : Plane →ₗᵢ[ℝ] Space := {
    fold.linear with
    norm_map' := fun x => by
      have difference := fold.linearMap_vsub x 0
      simp only [vsub_eq_sub, sub_zero] at difference
      rw [difference, ← dist_eq_norm, rigid.dist_eq, dist_zero_right] }
  let project := linear.toContinuousLinearMap.adjoint
  have bound : LipschitzWith 1 project := by
    simpa only [project, LinearIsometryEquiv.nnnorm_map, linear.nnnorm_toContinuousLinearMap]
      using project.lipschitz
  refine ⟨fun y => project (y - fold 0), ?_, ?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_sub_right] using bound.dist_le_mul (x - fold 0) (y - fold 0)
  · intro x
    change project (fold x - fold 0) = x
    have difference : fold x - fold 0 = linear x := by
      simpa only [vsub_eq_sub, sub_zero] using (fold.linearMap_vsub x 0).symm
    rw [difference]
    have identity := congrArg (fun f : Plane →L[ℝ] Plane => f x) linear.adjoint_comp_self
    exact identity

end SixVertexUnfolding
