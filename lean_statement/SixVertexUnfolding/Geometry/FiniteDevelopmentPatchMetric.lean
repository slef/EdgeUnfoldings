import SixVertexUnfolding.Geometry.FaceDevelopmentProjections
import SixVertexUnfolding.Geometry.ConvexFiniteSelection

/-! A radial development preserves distances on every convex surface
patch it contains. In particular this applies to small original-face patches. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- Finite rigid face formulas and a nonexpanding inverse give exact distances on a convex patch. -/
theorem finite_development_patch_isometric {P : ConvexPolyhedron} {F : P.Face}
    (region : Set (frontier P.body)) (planar : Set Plane) (H : region ≃ₜ planar)
    (pieces : ∀ x, ∃ piece : P.FaceDevelopmentPiece F,
      (x.val : Space) ∈ piece.face.val ∧ piece.place x.val = (H x : Plane))
    (inverse_bound : LipschitzWith 1 (fun z => ((H.symm z).val : Space)))
    (patch : Set Space) (convex_patch : Convex ℝ patch)
    (inclusion : C(patch, region)) (located : ∀ x, ((inclusion x).val : Space) = (x : Space)) :
    Isometry (fun x => (H (inclusion x) : Plane)) := by
  have forward : LipschitzWith 1 (fun x => (H (inclusion x) : Plane)) := by
    apply convex_subtype_finite_selection_lipschitz patch convex_patch
      (fun x => (H (inclusion x) : Plane)) (fun piece : P.FaceDevelopmentPiece F => piece.projectedPlace) 1
      (continuous_subtype_val.comp (H.continuous.comp inclusion.continuous))
      (fun piece => piece.projectedPlace_lipschitz.lipschitzOnWith)
    intro x
    obtain ⟨piece, inside, placed⟩ := pieces (inclusion x)
    refine ⟨piece, placed.symm.trans ?_⟩
    exact (piece.projectedPlace_on_face _ inside).symm.trans (congrArg piece.projectedPlace (located x))
  apply Isometry.of_dist_eq
  intro x y
  apply le_antisymm
  · simpa using forward.dist_le_mul x y
  · have bound := inverse_bound.dist_le_mul (H (inclusion x)) (H (inclusion y))
    simpa only [H.symm_apply_apply, located, NNReal.coe_one, one_mul] using bound

end SixVertexUnfolding.ConvexPolyhedron
