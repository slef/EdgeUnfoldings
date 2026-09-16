import SixVertexUnfolding.Geometry.RigidInverseProjection
import SixVertexUnfolding.Geometry.RadialStripDevelopments

/-! Each actual triangle development selects from finitely many
nonexpanding formulas on ambient space. These are derived from its
proved rigid inverse pieces, not assumed for the assembled map. -/

namespace SixVertexUnfolding.ConvexPolyhedron.RadialStripTriangle

open Set

variable {P : ConvexPolyhedron} {routes : C(unitInterval, P.BoundaryCurve)} {p l r : Plane}
    (D : RadialStripTriangle routes p l r)

theorem finite_forward_pieces :
    ∃ maps : Set (Space → Plane), maps.Finite ∧ (∀ g ∈ maps, LipschitzWith 1 g) ∧
      ∀ b : range (closedRouteStripMap routes), ∃ g ∈ maps, (D.homeomorph b : Plane) = g (b.val : Space) := by
  classical
  obtain ⟨folds, finite_folds, rigid, selected⟩ := D.rigid_pieces
  let inverse (f : folds) := (rigid_plane_inverse_extension f.val (rigid f.val f.property)).choose
  have inverse_spec (f : folds) : LipschitzWith 1 (inverse f) ∧ ∀ x, inverse f (f.val x) = x :=
    (rigid_plane_inverse_extension f.val (rigid f.val f.property)).choose_spec
  letI : Finite folds := finite_folds.to_subtype
  refine ⟨range inverse, finite_range inverse, ?_, ?_⟩
  · rintro _ ⟨f, rfl⟩
    exact (inverse_spec f).1
  · intro b
    obtain ⟨f, member, at_b⟩ := selected (D.homeomorph b)
    change ((D.homeomorph.symm (D.homeomorph b)).val : Space) = f (D.homeomorph b) at at_b
    rw [D.homeomorph.symm_apply_apply] at at_b
    refine ⟨inverse ⟨f, member⟩, mem_range_self _, ?_⟩
    rw [at_b]
    exact ((inverse_spec ⟨f, member⟩).2 (D.homeomorph b)).symm

end SixVertexUnfolding.ConvexPolyhedron.RadialStripTriangle
