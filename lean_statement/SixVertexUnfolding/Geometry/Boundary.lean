import SixVertexUnfolding.Geometry.Faces

/-! Supporting planes at boundary points, and boundary membership of every face. -/

namespace SixVertexUnfolding

/-- A nonzero normal defines a nonconstant, surjective height functional. -/
theorem inner_height_surjective {n : Space} (nonzero : n ≠ 0) :
    Function.Surjective (innerSL ℝ n) := by
  intro r
  refine ⟨(r / inner ℝ n n) • n, ?_⟩
  change inner ℝ n ((r / inner ℝ n n) • n) = r
  rw [inner_smul_right]
  exact div_mul_cancel₀ r (inner_self_ne_zero.mpr nonzero)

namespace ConvexPolyhedron

variable (P : ConvexPolyhedron)

/-- Every boundary point lies on a supporting plane with a nonzero normal.
This plane may initially touch a vertex or edge rather than a full facet. -/
theorem supporting_plane_at_boundary {x : Space} (boundary : x ∈ frontier P.body) :
    ∃ n : Space, n ≠ 0 ∧ ∀ y ∈ P.body, inner ℝ n y ≤ inner ℝ n x := by
  obtain ⟨height, nonzero, support⟩ := geometric_hahn_banach_of_nonempty_interior_point
    P.body_convex boundary.2 P.solid
  let n := (InnerProductSpace.toDual ℝ Space).symm height
  refine ⟨n, ?_, ?_⟩
  · intro zero
    apply nonzero
    ext y
    have evaluation : inner ℝ n y = height y := InnerProductSpace.toDual_symm_apply
    simpa [zero] using evaluation.symm
  · simpa [n, InnerProductSpace.toDual_symm_apply] using support

namespace Face

variable {P} (F : P.Face)

/-- Facets lie on the boundary; no point of a facet is an interior point of the solid. -/
theorem subset_frontier : F.val ⊆ frontier P.body := by
  obtain ⟨_, n, level, nonzero, support, face_eq⟩ := F.property
  intro x hx
  have on_plane : inner ℝ n x = level := (face_eq ▸ hx).2
  refine ⟨subset_closure (F.subset_body hx), ?_⟩
  intro inside
  have inclusion : P.body ⊆ (innerSL ℝ n) ⁻¹' Set.Iic level := support
  have height_strict := interior_mono inclusion inside
  rw [(innerSL ℝ n).interior_preimage (inner_height_surjective nonzero),
    interior_Iic] at height_strict
  change inner ℝ n x < level at height_strict
  linarith

end Face
end ConvexPolyhedron
end SixVertexUnfolding
