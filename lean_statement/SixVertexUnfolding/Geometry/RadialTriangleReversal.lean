import SixVertexUnfolding.Geometry.RadialStripDevelopments

/-! Reversing the edge parameter preserves the whole radial development,
once its three corners have been aligned by one rigid motion. -/

namespace SixVertexUnfolding.ConvexPolyhedron.RadialStripTriangle

open Set

variable {P : ConvexPolyhedron} {routes other : C(unitInterval, P.BoundaryCurve)}
    {p l r q L R : Plane} (D : RadialStripTriangle routes p l r)
    (E : RadialStripTriangle other q L R)

/-- Reversed route families sweep exactly the same closed surface region. -/
theorem reversed_family_range (same : ∀ t, routes t = other (unitInterval.symm t)) :
    range (closedRouteStripMap routes) = range (closedRouteStripMap other) := by
  ext x
  constructor
  · rintro ⟨⟨t, s⟩, at_x⟩
    refine ⟨(unitInterval.symm t, s), ?_⟩
    change other (unitInterval.symm t) s = x
    rw [← same]
    exact at_x
  · rintro ⟨⟨t, s⟩, at_x⟩
    refine ⟨(unitInterval.symm t, s), ?_⟩
    change routes (unitInterval.symm t) s = x
    rw [same, unitInterval.symm_symm]
    exact at_x

/-- A motion aligning the three corners aligns the complete surface maps,
not just an endpoint or a neighborhood of the edge. -/
theorem reversed_developments_agree (same : ∀ t, routes t = other (unitInterval.symm t))
    (motion : Plane ≃ᵃⁱ[ℝ] Plane) (source : motion p = q)
    (left : motion l = R) (right : motion r = L) :
    ∀ x : frontier P.body, ∀ hx : x ∈ range (closedRouteStripMap routes),
      ∀ hy : x ∈ range (closedRouteStripMap other),
        motion (D.homeomorph ⟨x, hx⟩) = (E.homeomorph ⟨x, hy⟩ : Plane) := by
  intro x hx hy
  have exists_x := hx
  obtain ⟨⟨t, s⟩, at_x⟩ := exists_x
  have other_x : closedRouteStripMap other (unitInterval.symm t, s) = x := by
    change other (unitInterval.symm t) s = x
    rw [← same]
    exact at_x
  have first : (D.homeomorph ⟨x, hx⟩ : Plane) = triangleFanMap p l r (t, s) := by
    have eq_point : (⟨x, hx⟩ : range (closedRouteStripMap routes)) =
        ⟨closedRouteStripMap routes (t, s), mem_range_self _⟩ := Subtype.ext at_x.symm
    rw [eq_point]
    exact D.radial (t, s)
  have second : (E.homeomorph ⟨x, hy⟩ : Plane) = triangleFanMap q L R (unitInterval.symm t, s) := by
    have eq_point : (⟨x, hy⟩ : range (closedRouteStripMap other)) =
        ⟨closedRouteStripMap other (unitInterval.symm t, s), mem_range_self _⟩ := Subtype.ext other_x.symm
    rw [eq_point]
    exact E.radial (unitInterval.symm t, s)
  rw [first, second]
  change motion.toAffineEquiv (AffineMap.lineMap p (AffineMap.lineMap l r (t : ℝ)) (s : ℝ)) = _
  rw [AffineEquiv.apply_lineMap, AffineEquiv.apply_lineMap]
  change AffineMap.lineMap (motion p) (AffineMap.lineMap (motion l) (motion r) (t : ℝ)) (s : ℝ) = _
  rw [source, left, right]
  change AffineMap.lineMap q (AffineMap.lineMap R L (t : ℝ)) (s : ℝ) =
    AffineMap.lineMap q (AffineMap.lineMap L R (1 - (t : ℝ))) (s : ℝ)
  rw [AffineMap.lineMap_apply_one_sub]

end SixVertexUnfolding.ConvexPolyhedron.RadialStripTriangle
