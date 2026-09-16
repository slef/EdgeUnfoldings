import SixVertexUnfolding.Geometry.ClosedCutRayIntersections
import SixVertexUnfolding.Geometry.ClosedStripFibers
import SixVertexUnfolding.Geometry.EmbeddedEdgeIntersections

/-! Closed strips over different cut-tree edges can meet only on
their endpoint rays. This uses their actual surface parametrizations. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- Every meeting of distinct closed-edge strips lies on an endpoint ray of the first strip. -/
theorem closed_strip_intersection_on_endpoint_rays (a : frontier P.body) (T : P.CutLocusTree a)
    {u v w z : T.vertices} (first : T.graph.Adj u v) (second : T.graph.Adj w z)
    (different : ¬ ((u = w ∧ v = z) ∨ (u = z ∧ v = w)))
    (routes other : C(unitInterval, P.BoundaryCurve))
    (member : ∀ t, routes t ∈ P.geodesicFiber a (T.closedEdgeTarget first t))
    (other_member : ∀ t, other t ∈ P.geodesicFiber a (T.closedEdgeTarget second t)) :
    range (closedRouteStripMap routes) ∩ range (closedRouteStripMap other) ⊆
      range (routes 0) ∪ range (routes 1) := by
  rintro x ⟨⟨⟨s, time⟩, rfl⟩, ⟨⟨t, other_time⟩, meet⟩⟩
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
  · left
    exact ⟨0, (congrArg Prod.fst (member 0).2).trans source.symm⟩
  ·
    have on_segment {i j : T.vertices} (edge : T.graph.Adj i j) (parameter : unitInterval) :
        (T.closedEdgeTarget edge parameter : Space) ∈ segment ℝ (i : Space) (j : Space) := by
      rw [segment_eq_image_lineMap]
      exact ⟨parameter, parameter.property, rfl⟩
    have endpoints := (T.toEmbeddedCutGraph.distinct_edges_meet_at_endpoints first second different
      (on_segment first s) (by rw [targets]; exact on_segment second t)).1
    have at_zero : T.closedEdgeTarget first s = T.closedEdgeTarget first 0 → s = 0 :=
      fun h => T.closedEdgeTarget_injective first h
    have at_one : T.closedEdgeTarget first s = T.closedEdgeTarget first 1 → s = 1 :=
      fun h => T.closedEdgeTarget_injective first h
    rcases endpoints with left | right
    · have zero := at_zero (by rw [T.closedEdgeTarget_zero]; exact Subtype.ext left)
      exact Or.inl ⟨time, by change routes 0 time = routes s time; rw [zero]⟩
    · have one := at_one (by rw [T.closedEdgeTarget_one]; exact Subtype.ext right)
      exact Or.inr ⟨time, by change routes 1 time = routes s time; rw [one]⟩

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
