import SixVertexUnfolding.Geometry.RadialTriangleAlignment

/-! Moving a radial development by a rigid planar motion preserves all
its surface correspondence and metric guarantees. -/

namespace SixVertexUnfolding

open Set

/-- A rigid motion preserves nondegeneracy of a triangle. -/
theorem plane_motion_noncollinear (motion : Plane ≃ᵃⁱ[ℝ] Plane) (p l r : Plane)
    (noncollinear : ¬ Collinear ℝ ({p, l, r} : Set Plane)) :
    ¬ Collinear ℝ ({motion p, motion l, motion r} : Set Plane) := by
  apply affineIndependent_iff_not_collinear_set.mp
  have mapped := (affineIndependent_iff_not_collinear_set.mpr noncollinear).map'
    motion.toAffineMap motion.injective
  convert mapped using 1
  ext i
  fin_cases i <;> rfl

/-- Restrict a rigid motion to a closed triangle and its image triangle. -/
noncomputable def triangleMotion (motion : Plane ≃ᵃⁱ[ℝ] Plane) (p l r : Plane) :
    convexHull ℝ ({p, l, r} : Set Plane) ≃ₜ
      convexHull ℝ ({motion p, motion l, motion r} : Set Plane) :=
  (motion.toHomeomorph.image _).trans (Homeomorph.setCongr (by
    change motion.toAffineMap '' convexHull ℝ ({p, l, r} : Set Plane) = _
    rw [motion.toAffineMap.image_convexHull]
    simp only [image_insert_eq, image_singleton]
    rfl))

@[simp] theorem triangleMotion_apply (motion : Plane ≃ᵃⁱ[ℝ] Plane) (p l r : Plane)
    (x : convexHull ℝ ({p, l, r} : Set Plane)) :
    (triangleMotion motion p l r x : Plane) = motion x := rfl

theorem triangleMotion_isometry (motion : Plane ≃ᵃⁱ[ℝ] Plane) (p l r : Plane) :
    Isometry (triangleMotion motion p l r) := by
  apply isometry_iff_dist_eq.mpr
  intro x y
  exact motion.dist_map x y

theorem triangleMotion_symm_isometry (motion : Plane ≃ᵃⁱ[ℝ] Plane) (p l r : Plane) :
    Isometry (triangleMotion motion p l r).symm := by
  apply isometry_iff_dist_eq.mpr
  intro x y
  simpa using ((triangleMotion_isometry motion p l r).dist_eq
    ((triangleMotion motion p l r).symm x) ((triangleMotion motion p l r).symm y)).symm

namespace ConvexPolyhedron.RadialStripTriangle

variable {P : ConvexPolyhedron} {routes : C(unitInterval, P.BoundaryCurve)} {p l r : Plane}
  (D : RadialStripTriangle routes p l r)

/-- Translate, rotate or reflect a triangle development without changing its surface data. -/
noncomputable def move (motion : Plane ≃ᵃⁱ[ℝ] Plane) :
    RadialStripTriangle routes (motion p) (motion l) (motion r) where
  homeomorph := D.homeomorph.trans (triangleMotion motion p l r)
  radial := by
    intro z
    change motion (D.homeomorph _) = _
    rw [D.radial]
    change motion.toAffineEquiv (AffineMap.lineMap p (AffineMap.lineMap l r (z.1 : ℝ)) (z.2 : ℝ)) = _
    rw [AffineEquiv.apply_lineMap, AffineEquiv.apply_lineMap]
    rfl
  inverse_nonexpanding := by
    simpa only [one_mul] using D.inverse_nonexpanding.comp
      (triangleMotion_symm_isometry motion p l r).lipschitz
  convex_patches := by
    intro patch convex_patch inclusion located
    exact motion.isometry.comp (D.convex_patches patch convex_patch inclusion located)
  flat_patches := by
    intro z chart patch convex_patch in_domain inclusion located
    exact motion.isometry.comp (D.flat_patches chart patch convex_patch in_domain inclusion located)
  rigid_pieces := by
    obtain ⟨maps, finite_maps, rigid, selected⟩ := D.rigid_pieces
    refine ⟨(fun f : Plane →ᵃ[ℝ] Space => f.comp motion.symm.toAffineMap) '' maps,
      finite_maps.image _, ?_, ?_⟩
    · rintro _ ⟨f, member, rfl⟩
      exact (rigid f member).comp motion.symm.isometry
    · intro z
      obtain ⟨f, member, agrees⟩ := selected ((triangleMotion motion p l r).symm z)
      refine ⟨f.comp motion.symm.toAffineMap, ⟨f, member, rfl⟩, agrees.trans ?_⟩
      rfl

@[simp] theorem move_apply (motion : Plane ≃ᵃⁱ[ℝ] Plane)
    (x : range (closedRouteStripMap routes)) :
    ((D.move motion).homeomorph x : Plane) = motion (D.homeomorph x) := rfl

/-- Align a shared route while retaining a complete triangle-development record. -/
theorem move_agrees_on_shared_route {other : C(unitInterval, P.BoundaryCurve)} {q u v : Plane}
    (E : RadialStripTriangle other q u v) (s t : unitInterval)
    (same_route : routes s = other t)
    (same_length : dist p (AffineMap.lineMap l r (s : ℝ)) =
      dist q (AffineMap.lineMap u v (t : ℝ))) :
    ∃ motion : Plane ≃ᵃⁱ[ℝ] Plane, motion p = q ∧
      ∀ x ∈ range (routes s), ∀ hx : x ∈ range (closedRouteStripMap routes),
        ∀ hy : x ∈ range (closedRouteStripMap other),
          ((D.move motion).homeomorph ⟨x, hx⟩ : Plane) = (E.homeomorph ⟨x, hy⟩ : Plane) :=
  D.align_shared_route E s t same_route same_length

end ConvexPolyhedron.RadialStripTriangle
end SixVertexUnfolding
