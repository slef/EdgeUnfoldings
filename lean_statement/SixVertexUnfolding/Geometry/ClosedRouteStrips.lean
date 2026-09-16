import SixVertexUnfolding.Geometry.RouteStrips
import Mathlib.Topology.Constructions

/-! Closing a continuous route family closes its swept strip exactly.
The only added parameters are the two endpoint routes, the target edge,
and the common source. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set BoundedContinuousFunction

/-- Evaluate a route family including both edge endpoints and both route endpoints. -/
noncomputable def closedRouteStripMap {P : ConvexPolyhedron}
    (routes : C(unitInterval, P.BoundaryCurve)) : C(unitInterval × unitInterval, frontier P.body) :=
  ⟨fun p => routes p.1 p.2,
    continuous_eval.comp ((routes.continuous.comp continuous_fst).prodMk continuous_snd)⟩

/-- Interior times are dense in the closed unit interval. -/
theorem interiorTime_dense : DenseRange interiorTime := by
  change DenseRange (inclusion (Ioo_subset_Icc_self : Ioo (0 : ℝ) 1 ⊆ Icc 0 1))
  rw [denseRange_inclusion_iff, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]

/-- The closed swept region is precisely the closure of its open strip. -/
theorem closure_routeStrip_eq {P : ConvexPolyhedron}
    (open_routes : C(Ioo (0 : ℝ) 1, P.BoundaryCurve))
    (closed_routes : C(unitInterval, P.BoundaryCurve))
    (agrees : ∀ t, closed_routes (interiorTime t) = open_routes t) :
    closure (routeStrip open_routes) = range (closedRouteStripMap closed_routes) := by
  let inclusion : Ioo (0 : ℝ) 1 × Ioo (0 : ℝ) 1 → unitInterval × unitInterval :=
    Prod.map interiorTime interiorTime
  have dense : DenseRange inclusion := interiorTime_dense.prodMap interiorTime_dense
  have same : closedRouteStripMap closed_routes ∘ inclusion = routeStripMap open_routes := by
    funext p
    exact congrFun (congrArg DFunLike.coe (agrees p.1)) (interiorTime p.2)
  have included : routeStrip open_routes ⊆ range (closedRouteStripMap closed_routes) := by
    rw [routeStrip, ← same]
    exact range_comp_subset_range _ _
  apply Subset.antisymm (closure_minimal included (isCompact_range (closedRouteStripMap closed_routes).continuous).isClosed)
  have contains := (closedRouteStripMap closed_routes).continuous.range_subset_closure_image_dense dense
  rwa [← range_comp, same] at contains

/-- Any point added by closure lies on an endpoint route, the target edge, or the source. -/
theorem closed_route_strip_added_points {P : ConvexPolyhedron} (a : frontier P.body)
    (target : unitInterval → frontier P.body)
    (open_routes : C(Ioo (0 : ℝ) 1, P.BoundaryCurve))
    (closed_routes : C(unitInterval, P.BoundaryCurve))
    (agrees : ∀ t, closed_routes (interiorTime t) = open_routes t)
    (member : ∀ t, closed_routes t ∈ P.geodesicFiber a (target t))
    (b : frontier P.body) (added : b ∈ closure (routeStrip open_routes) \ routeStrip open_routes) :
    b = a ∨ b ∈ range target ∨ b ∈ range (closed_routes 0) ∨ b ∈ range (closed_routes 1) := by
  rw [closure_routeStrip_eq open_routes closed_routes agrees] at added
  obtain ⟨⟨x, t⟩, at_point⟩ := added.1
  have at_point' : closed_routes x t = b := at_point
  by_cases time_zero : t = 0
  · exact Or.inl (at_point'.symm.trans (time_zero ▸ congrArg Prod.fst (member x).2))
  by_cases time_one : t = 1
  · right; left
    exact ⟨x, (congrArg Prod.snd (member x).2).symm.trans (by simpa only [time_one] using at_point')⟩
  by_cases edge_zero : x = 0
  · right; right; left
    exact ⟨t, edge_zero ▸ at_point'⟩
  by_cases edge_one : x = 1
  · right; right; right
    exact ⟨t, edge_one ▸ at_point'⟩
  have x_inside : 0 < x ∧ x < 1 := ⟨lt_of_le_of_ne x.property.1 (Ne.symm edge_zero),
    lt_of_le_of_ne x.property.2 edge_one⟩
  have t_inside : 0 < t ∧ t < 1 := ⟨lt_of_le_of_ne t.property.1 (Ne.symm time_zero),
    lt_of_le_of_ne t.property.2 time_one⟩
  exfalso
  apply added.2
  refine ⟨(⟨x, x_inside⟩, ⟨t, t_inside⟩), ?_⟩
  change open_routes ⟨x, x_inside⟩ t = b
  rw [← agrees]
  exact at_point'

end SixVertexUnfolding.ConvexPolyhedron
