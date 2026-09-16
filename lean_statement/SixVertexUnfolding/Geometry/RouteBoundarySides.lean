import SixVertexUnfolding.Geometry.TwoSidedBoundary
import SixVertexUnfolding.Geometry.ShortestRouteLine

/-! A shortest route has only two local sides at each nonvertex interior
point, expressed for actual open regions of the polyhedral boundary. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- Three disjoint surface regions cannot share only one shortest-route
boundary near the same interior point. -/
theorem not_three_regions_along_route (P : ConvexPolyhedron) (a b : frontier P.body)
    (different : a ≠ b) (f : P.BoundaryCurve) (member : f ∈ P.geodesicFiber a b)
    (m : unitInterval) (after_start : 0 < m) (before_end : m < 1)
    (nonvertex : (f m : Space) ∉ P.vertices)
    (regions : Fin 3 → Set (frontier P.body)) (open_regions : ∀ i, IsOpen (regions i))
    (separate : Pairwise (fun i j => Disjoint (regions i) (regions j)))
    (limits : ∀ i, f m ∈ closure (regions i))
    (U : Set (frontier P.body)) (openU : IsOpen U) (center : f m ∈ U)
    (boundaries : ∀ i, frontier (regions i) ∩ U ⊆ range f) : False := by
  obtain ⟨chart, normal, height, radius, nonzero, positive, domain, line⟩ :=
    P.shortest_route_line_chart a b different f member m after_start before_end nonvertex
  have at_center : chart.surfaceMap ⟨chart.origin, chart.origin_mem⟩ = f m :=
    Subtype.ext chart.at_origin
  have centerU : chart.origin ∈ chart.pullback U :=
    (chart.mem_pullback U chart.origin chart.origin_mem).mpr (at_center.symm ▸ center)
  obtain ⟨ε, εpos, nearU⟩ := Metric.isOpen_iff.mp (chart.pullback_open openU) chart.origin centerU
  let r := min radius ε
  have rpos : 0 < r := lt_min positive εpos
  have in_radius {x : Plane} (hx : x ∈ Metric.ball chart.origin r) :
      x ∈ Metric.ball chart.origin radius :=
    lt_of_lt_of_le (show dist x chart.origin < min radius ε from hx) (min_le_left _ _)
  have in_U {x : Plane} (hx : x ∈ Metric.ball chart.origin r) : x ∈ chart.pullback U :=
    nearU (lt_of_lt_of_le (show dist x chart.origin < min radius ε from hx) (min_le_right _ _))
  apply not_three_regions_at_line (fun i => chart.pullback (regions i))
    (fun i => chart.pullback_open (open_regions i))
    (fun _ _ different => chart.pullback_disjoint (separate different))
    chart.origin normal nonzero height r rpos
    (fun i => chart.center_mem_closure_pullback (regions i) (f m) rfl (limits i))
  intro i x hx
  have in_domain := domain (in_radius hx.2)
  have surface_boundary := chart.frontier_pullback (open_regions i) x in_domain hx.1
  have surfaceU := (chart.mem_pullback U x in_domain).mp (in_U hx.2)
  exact line x (in_radius hx.2)
    ⟨chart.surfaceMap ⟨x, in_domain⟩, boundaries i ⟨surface_boundary, surfaceU⟩, rfl⟩

end SixVertexUnfolding.ConvexPolyhedron
