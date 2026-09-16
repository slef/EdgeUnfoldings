import SixVertexUnfolding.Geometry.NormalizedFacetPlanes

/-! Three different facet planes meeting at a point admit independent height coordinates. -/

namespace SixVertexUnfolding.ConvexPolyhedron.NormalizedFacets

variable {P : ConvexPolyhedron} {center : Space} (facets : NormalizedFacets P center)

/-- At a common point of three extended facet planes, their normals are linearly independent. -/
theorem independent_at_common_point (A B C : P.Face) (ab : A ≠ B) (ac : A ≠ C) (bc : B ≠ C)
    (o : Space) (oA : o ∈ affineSpan ℝ A.val) (oB : o ∈ affineSpan ℝ B.val)
    (oC : o ∈ affineSpan ℝ C.val) :
    LinearIndependent ℝ ![facets.normal A, facets.normal B, facets.normal C] := by
  let normals : Fin 3 → Space := ![facets.normal A, facets.normal B, facets.normal C]
  have affine : AffineIndependent ℝ normals :=
    affineIndependent_iff_not_collinear_set.mpr (facets.no_three_collinear A B C ab ac bc)
  have height (i : Fin 3) : inner ℝ (normals i) (o - center) = 1 := by
    fin_cases i
    exacts [facets.on_plane A oA, facets.on_plane B oB, facets.on_plane C oC]
  apply Fintype.linearIndependent_iff.mpr
  intro w combination
  change ∑ i, w i • normals i = 0 at combination
  have sum_zero : ∑ i, w i = 0 := by
    have measured := congrArg (fun v : Space => inner ℝ v (o - center)) combination
    simpa only [sum_inner, real_inner_smul_left, height, mul_one, inner_zero_left] using measured
  apply (affineIndependent_iff_of_fintype ℝ normals).mp affine w sum_zero
  simpa only [Finset.weightedVSub_eq_linear_combination _ sum_zero] using combination

/-- Any three prescribed support heights can be realized when the three planes meet. -/
theorem exists_prescribed_heights (A B C : P.Face) (ab : A ≠ B) (ac : A ≠ C) (bc : B ≠ C)
    (o : Space) (oA : o ∈ affineSpan ℝ A.val) (oB : o ∈ affineSpan ℝ B.val)
    (oC : o ∈ affineSpan ℝ C.val) (a b c : ℝ) :
    ∃ z : Space, inner ℝ (facets.normal A) (z - center) = a ∧
      inner ℝ (facets.normal B) (z - center) = b ∧
      inner ℝ (facets.normal C) (z - center) = c := by
  let normals : Fin 3 → Space := ![facets.normal A, facets.normal B, facets.normal C]
  let heights : Space →ₗ[ℝ] (Fin 3 → ℝ) :=
    LinearMap.pi fun i => (innerSL ℝ (normals i)).toLinearMap
  have independent := facets.independent_at_common_point A B C ab ac bc o oA oB oC
  have span_top : Submodule.span ℝ (Set.range normals) = ⊤ :=
    independent.span_eq_top_of_card_eq_finrank (by simp [Space])
  have injective : Function.Injective heights := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x zero
    have vanishes : Submodule.span ℝ (Set.range normals) ≤ (innerSL ℝ x).toLinearMap.ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      change inner ℝ x (normals i) = 0
      rw [real_inner_comm]
      exact congrFun zero i
    have at_x := vanishes (span_top ▸ (Submodule.mem_top : x ∈ (⊤ : Submodule ℝ Space)))
    exact inner_self_eq_zero.mp at_x
  have onto : Function.Surjective heights :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [Space])).mp injective
  obtain ⟨v, equal⟩ := onto ![a, b, c]
  refine ⟨v + center, ?_, ?_, ?_⟩
  · simpa only [add_sub_cancel_right] using congrFun equal 0
  · simpa only [add_sub_cancel_right] using congrFun equal 1
  · simpa only [add_sub_cancel_right] using congrFun equal 2

end SixVertexUnfolding.ConvexPolyhedron.NormalizedFacets
