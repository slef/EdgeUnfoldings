import SixVertexUnfolding.Geometry.GeodesicCurvePaths

/-! Compactness makes the family of normalized shortest routes stable when
the endpoints move. A unique route attracts every nearby-endpoint route. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set BoundedContinuousFunction

/-- Source and target together, viewed as points of the actual boundary. -/
noncomputable def curveEndpoints (P : ConvexPolyhedron) (f : P.BoundaryCurve) :
    (frontier P.body) × (frontier P.body) :=
  (f 0, f 1)

theorem curveEndpoints_continuous (P : ConvexPolyhedron) : Continuous P.curveEndpoints :=
  (continuous_eval_const 0).prodMk (continuous_eval_const 1)

/-- An open neighborhood of all routes for one endpoint pair contains all routes for nearby pairs. -/
theorem geodesic_family_upper_continuous (P : ConvexPolyhedron)
    (ends : (frontier P.body) × (frontier P.body)) (U : Set P.BoundaryCurve) (openU : IsOpen U)
    (contains : ∀ f ∈ P.geodesicCurves, P.curveEndpoints f = ends → f ∈ U) :
    ∃ V : Set ((frontier P.body) × (frontier P.body)), IsOpen V ∧ ends ∈ V ∧
      ∀ f ∈ P.geodesicCurves, P.curveEndpoints f ∈ V → f ∈ U := by
  let bad := P.geodesicCurves \ U
  have compact_bad : IsCompact bad := P.geodesicCurves_compact.diff openU
  have closed_image : IsClosed (P.curveEndpoints '' bad) :=
    (compact_bad.image P.curveEndpoints_continuous).isClosed
  refine ⟨(P.curveEndpoints '' bad)ᶜ, closed_image.isOpen_compl, ?_, ?_⟩
  · rintro ⟨f, hf, endpoints⟩
    exact hf.2 (contains f hf.1 endpoints)
  · intro f geodesic near
    by_contra outside
    exact near ⟨f, ⟨geodesic, outside⟩, rfl⟩

/-- At a unique geodesic, moving the endpoints keeps every geodesic uniformly near it. -/
theorem unique_geodesic_stability (P : ConvexPolyhedron) (f : P.BoundaryCurve)
    (unique : ∀ g ∈ P.geodesicCurves, P.curveEndpoints g = P.curveEndpoints f → g = f)
    (U : Set P.BoundaryCurve) (openU : IsOpen U) (contains : f ∈ U) :
    ∃ V : Set ((frontier P.body) × (frontier P.body)), IsOpen V ∧ P.curveEndpoints f ∈ V ∧
      ∀ g ∈ P.geodesicCurves, P.curveEndpoints g ∈ V → g ∈ U :=
  P.geodesic_family_upper_continuous (P.curveEndpoints f) U openU
    (fun g hg ends => unique g hg ends ▸ contains)

end SixVertexUnfolding.ConvexPolyhedron
