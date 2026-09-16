import SixVertexUnfolding.Geometry.OpenCutEdgeStrips
import SixVertexUnfolding.Geometry.ClosedCutRayIntersections

/-! Near an interior point of an endpoint route, the only boundary of
an incident strip is that route. Other strip boundaries are compact and
avoid the chosen point. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- The endpoint route is the entire possible local boundary of one strip. -/
theorem strip_frontier_near_endpoint_route (a : frontier P.body) (T : P.CutLocusTree a)
    {u v : T.vertices} (edge : T.graph.Adj u v)
    (open_routes : C(Ioo (0 : ℝ) 1, P.BoundaryCurve))
    (routes : C(unitInterval, P.BoundaryCurve))
    (agrees : ∀ t, routes (interiorTime t) = open_routes t)
    (member : ∀ t, routes t ∈ P.geodesicFiber a (T.closedEdgeTarget edge t))
    (open_strip : IsOpen (routeStrip open_routes))
    (m : unitInterval) (after_start : 0 < m) (before_end : m < 1) :
    routes 0 m ∈ closure (routeStrip open_routes) ∧
    ∃ U : Set (frontier P.body), IsOpen U ∧ routes 0 m ∈ U ∧
      frontier (routeStrip open_routes) ∩ U ⊆ range (routes 0) := by
  have first : routes 0 0 = a := congrArg Prod.fst (member 0).2
  have last : routes 0 1 = T.vertexTarget u := by
    simpa only [T.closedEdgeTarget_zero] using congrArg Prod.snd (member 0).2
  have distinct : a ≠ T.vertexTarget u := by
    intro same
    have cut := T.vertexTarget_cut u
    rw [← same] at cut
    exact P.source_not_cutSet a cut
  have endpoint_member : routes 0 ∈ P.geodesicFiber a (T.vertexTarget u) := by
    simpa only [T.closedEdgeTarget_zero] using member 0
  have injective := P.geodesicFiber_injective a (T.vertexTarget u) distinct (routes 0) endpoint_member
  have not_source : routes 0 m ≠ a := fun same =>
    after_start.ne' (injective (same.trans first.symm))
  have not_cut : routes 0 m ∉ P.cutSet a := by
    have outside := graph.geodesic_proper_prefix_outside_cutSet small_faces (routes 0)
      (member 0).1 (by simpa only [first, last] using distinct) m before_end
    simpa only [first] using outside
  have not_other : routes 0 m ∉ range (routes 1) := by
    intro inside
    have intersections := graph.closed_cut_rays_intersection_of_distinct_targets small_faces a
      (T.vertexTarget u) (T.vertexTarget v) (T.vertexTarget_cut u) (T.vertexTarget_cut v)
      (fun same => edge.ne (Subtype.ext
        (congrArg (fun b : frontier P.body => (b : Space)) same)))
      (routes 0) (routes 1) endpoint_member
      (by simpa only [T.closedEdgeTarget_one] using member 1)
    have at_source : routes 0 m ∈ ({a} : Set (frontier P.body)) :=
      intersections ▸ ⟨mem_range_self m, inside⟩
    exact not_source at_source
  let bad : Set (frontier P.body) := {a} ∪ P.cutSet a ∪ range (routes 1)
  have closed : IsClosed bad :=
    (isClosed_singleton.union (graph.cutSet_closed small_faces a)).union
      (isCompact_range (routes 1).continuous).isClosed
  have center : routes 0 m ∉ bad := by
    rintro ((source | cut) | other)
    · exact not_source source
    · exact not_cut cut
    · exact not_other other
  refine ⟨?_, badᶜ, closed.isOpen_compl, center, ?_⟩
  · rw [closure_routeStrip_eq open_routes routes agrees]
    exact ⟨(0, m), rfl⟩
  · rintro x ⟨boundary, outside⟩
    have added : x ∈ closure (routeStrip open_routes) \ routeStrip open_routes :=
      ⟨boundary.1, by simpa only [open_strip.interior_eq] using boundary.2⟩
    rcases closed_route_strip_added_points a (T.closedEdgeTarget edge) open_routes routes
        agrees member x added with source | ⟨t, rfl⟩ | on_route | other
    · exact (outside (Or.inl (Or.inl source))).elim
    · exact (outside (Or.inl (Or.inr (T.closedEdgeTarget_cut edge t)))).elim
    · exact on_route
    · exact (outside (Or.inr other)).elim

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
