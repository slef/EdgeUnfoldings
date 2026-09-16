import SixVertexUnfolding.Geometry.ClosedStripBoundaryIntersections

/-! The exact surface overlap of strips over successive, distinct
tree edges is the intersection of their two routes to the common vertex. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

namespace CutLocusTree

variable {P : ConvexPolyhedron} {a : frontier P.body} (T : P.CutLocusTree a)

theorem successive_targets_equal {u v w : T.vertices}
    (first : T.graph.Adj u v) (second : T.graph.Adj v w) (no_return : u ≠ w)
    (s t : unitInterval) :
    T.closedEdgeTarget first s = T.closedEdgeTarget second t ↔ s = 1 ∧ t = 0 := by
  constructor
  · intro same
    have different : ¬ ((u = v ∧ v = w) ∨ (u = w ∧ v = v)) := by
      rintro (⟨equal, _⟩ | ⟨equal, _⟩)
      · exact first.ne equal
      · exact no_return equal
    have on_segment {i j : T.vertices} (edge : T.graph.Adj i j) (parameter : unitInterval) :
        (T.closedEdgeTarget edge parameter : Space) ∈ segment ℝ (i : Space) (j : Space) := by
      rw [segment_eq_image_lineMap]
      exact ⟨parameter, parameter.property, rfl⟩
    obtain ⟨left, right⟩ := T.toEmbeddedCutGraph.distinct_edges_meet_at_endpoints
      first second different (on_segment first s) (by rw [same]; exact on_segment second t)
    have common : (T.closedEdgeTarget first s : Space) = (v : Space) := by
      rcases left with at_u | at_v
      · rcases right with at_v | at_w
        · exact False.elim (first.ne (Subtype.ext (at_u.symm.trans at_v)))
        · exact False.elim (no_return (Subtype.ext (at_u.symm.trans at_w)))
      · exact at_v
    constructor
    · apply T.closedEdgeTarget_injective first
      rw [T.closedEdgeTarget_one]
      exact Subtype.ext common
    · apply T.closedEdgeTarget_injective second
      rw [T.closedEdgeTarget_zero, ← same]
      exact Subtype.ext common
  · rintro ⟨rfl, rfl⟩
    rw [T.closedEdgeTarget_one, T.closedEdgeTarget_zero]

end CutLocusTree

namespace SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- Only the routes to the shared vertex can belong to both successive closed strips. -/
theorem successive_strips_intersection (a : frontier P.body) (T : P.CutLocusTree a)
    {u v w : T.vertices} (first : T.graph.Adj u v) (second : T.graph.Adj v w) (no_return : u ≠ w)
    (routes other : C(unitInterval, P.BoundaryCurve))
    (member : ∀ t, routes t ∈ P.geodesicFiber a (T.closedEdgeTarget first t))
    (other_member : ∀ t, other t ∈ P.geodesicFiber a (T.closedEdgeTarget second t)) :
    range (closedRouteStripMap routes) ∩ range (closedRouteStripMap other) =
      range (routes 1) ∩ range (other 0) := by
  apply Subset.antisymm
  · rintro x ⟨⟨⟨s, time⟩, rfl⟩, ⟨⟨t, other_time⟩, meet⟩⟩
    change other t other_time = routes s time at meet
    have intersections := (graph.closed_cut_rays_intersection small_faces a
      (T.closedEdgeTarget first s) (T.closedEdgeTarget second t)
      (T.closedEdgeTarget_cut first s) (T.closedEdgeTarget_cut second t)
      (routes s) (other t) (member s) (other_member t) (routes s time)).mp
        ⟨mem_range_self time, ⟨other_time, meet⟩⟩
    have alternatives : routes s time = a ∨ T.closedEdgeTarget first s = T.closedEdgeTarget second t := by
      rcases intersections with source | ⟨targets, _⟩ | ⟨same_routes, _⟩
      · exact Or.inl source
      · exact Or.inr targets
      · right
        exact (congrArg Prod.snd (member s).2).symm.trans
          ((congrArg (fun route : P.BoundaryCurve => route 1) same_routes).trans
            (congrArg Prod.snd (other_member t).2))
    rcases alternatives with source | targets
    · exact ⟨⟨0, (congrArg Prod.fst (member 1).2).trans source.symm⟩,
        ⟨0, (congrArg Prod.fst (other_member 0).2).trans source.symm⟩⟩
    · obtain ⟨rfl, rfl⟩ := (T.successive_targets_equal first second no_return s t).mp targets
      exact ⟨mem_range_self time, ⟨other_time, meet⟩⟩
  · rintro x ⟨⟨time, left⟩, ⟨other_time, right⟩⟩
    exact ⟨⟨(1, time), left⟩, ⟨(0, other_time), right⟩⟩

include graph small_faces in
/-- With a shared endpoint route, the closed strips overlap along exactly that route. -/
theorem successive_strips_intersection_of_shared_route (a : frontier P.body) (T : P.CutLocusTree a)
    {u v w : T.vertices} (first : T.graph.Adj u v) (second : T.graph.Adj v w) (no_return : u ≠ w)
    (routes other : C(unitInterval, P.BoundaryCurve))
    (member : ∀ t, routes t ∈ P.geodesicFiber a (T.closedEdgeTarget first t))
    (other_member : ∀ t, other t ∈ P.geodesicFiber a (T.closedEdgeTarget second t))
    (same_route : routes 1 = other 0) :
    range (closedRouteStripMap routes) ∩ range (closedRouteStripMap other) = range (routes 1) := by
  rw [graph.successive_strips_intersection small_faces a T first second no_return routes other member other_member,
    ← same_route, inter_self]

end SixVertexGraph
end SixVertexUnfolding.ConvexPolyhedron
