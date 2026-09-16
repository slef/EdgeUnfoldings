import SixVertexUnfolding.Geometry.OpenPlaneRigidity
import Mathlib.Topology.LocallyConstant.Basic

/-! Rigid motions determined on overlapping open patches agree. Consequently,
a locally rigid planar map on a connected region is one rigid motion. -/

namespace SixVertexUnfolding

open Set

/-- Local rigid motions cannot change as one moves through a connected region. -/
theorem connected_plane_local_motions (region : Set Plane)
    (nonempty : region.Nonempty) (connected : IsPreconnected region) (f : region → Plane)
    (patches : ∀ x : region, ∃ U : Set Plane, IsOpen U ∧ (x : Plane) ∈ U ∧
      ∃ inside : U ⊆ region, ∃ motion : Plane ≃ᵃⁱ[ℝ] Plane,
        ∀ y : U, motion y = f ⟨y, inside y.property⟩) :
    ∃ motion : Plane ≃ᵃⁱ[ℝ] Plane, ∀ x : region, motion x = f x := by
  classical
  choose U open_U center inside motion agrees using patches
  letI : PreconnectedSpace region := isPreconnected_iff_preconnectedSpace.mp connected
  have locally_constant : IsLocallyConstant motion := by
    apply (IsLocallyConstant.iff_exists_open motion).mpr
    intro x
    refine ⟨Subtype.val ⁻¹' U x, (open_U x).preimage continuous_subtype_val, center x, ?_⟩
    intro y yU
    have spans : affineSpan ℝ (U x ∩ U y) = ⊤ :=
      ((open_U x).inter (open_U y)).affineSpan_eq_top ⟨y, yU, center y⟩
    have same : (motion y).toAffineMap = (motion x).toAffineMap := by
      apply AffineMap.ext_on spans
      intro z hz
      exact (agrees y ⟨z, hz.2⟩).trans (agrees x ⟨z, hz.1⟩).symm
    apply DFunLike.ext
    intro z
    exact congrArg (fun g : Plane →ᵃ[ℝ] Plane => g z) same
  obtain ⟨x, hx⟩ := nonempty
  refine ⟨motion ⟨x, hx⟩, ?_⟩
  intro y
  rw [locally_constant.apply_eq_of_preconnectedSpace ⟨x, hx⟩ y]
  exact agrees y ⟨y, center y⟩

end SixVertexUnfolding
