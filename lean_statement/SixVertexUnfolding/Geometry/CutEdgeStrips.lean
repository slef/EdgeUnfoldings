import SixVertexUnfolding.Geometry.CutEdgeRouteBranches
import SixVertexUnfolding.Geometry.RouteStripCoverage

/-! The two shortest-route strips attached to an actual open cut-tree edge.
Their parameters are one point of that edge and one interior route time. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- Two continuously labelled shortest-route families over one open tree edge. -/
structure CutEdgeStrips {P : ConvexPolyhedron} {a : frontier P.body}
    (T : P.CutLocusTree a) {u v : T.vertices} (edge : T.graph.Adj u v) where
  first : C(Ioo (0 : ℝ) 1, P.BoundaryCurve)
  second : C(Ioo (0 : ℝ) 1, P.BoundaryCurve)
  distinct : ∀ t, first t ≠ second t
  fiber : ∀ t, P.geodesicFiber a (T.openEdgeTarget edge t) = {first t, second t}

namespace CutEdgeStrips

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a}
  {u v : T.vertices} {edge : T.graph.Adj u v} (S : CutEdgeStrips T edge)

theorem first_member (t : Ioo (0 : ℝ) 1) :
    S.first t ∈ P.geodesicFiber a (T.openEdgeTarget edge t) := by rw [S.fiber]; simp

theorem second_member (t : Ioo (0 : ℝ) 1) :
    S.second t ∈ P.geodesicFiber a (T.openEdgeTarget edge t) := by rw [S.fiber]; simp

end CutEdgeStrips

namespace SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
theorem exists_cut_edge_strips (a : frontier P.body) (T : P.CutLocusTree a)
    {u v : T.vertices} (edge : T.graph.Adj u v) : Nonempty (CutEdgeStrips T edge) := by
  obtain ⟨first, second, distinct, pair⟩ := graph.cut_edge_continuous_routes small_faces a T edge
  exact ⟨⟨first, second, distinct, pair⟩⟩

include graph small_faces in
/-- Each strip is parametrized without identifying distinct points. -/
theorem cut_edge_strips_injective (a : frontier P.body) (T : P.CutLocusTree a)
    {u v : T.vertices} (edge : T.graph.Adj u v) (S : CutEdgeStrips T edge) :
    Function.Injective (routeStripMap S.first) ∧ Function.Injective (routeStripMap S.second) := by
  have cut t := T.open_edge_cut edge (T.openEdgeTarget edge t) (T.openEdgeTarget_inside edge t)
  exact ⟨graph.routeStripMap_injective small_faces a _ (T.openEdgeTarget_injective edge)
      cut S.first S.first_member,
    graph.routeStripMap_injective small_faces a _ (T.openEdgeTarget_injective edge)
      cut S.second S.second_member⟩

include graph small_faces in
/-- The two sides of the same edge have disjoint swept interiors. -/
theorem cut_edge_strips_disjoint (a : frontier P.body) (T : P.CutLocusTree a)
    {u v : T.vertices} (edge : T.graph.Adj u v) (S : CutEdgeStrips T edge) :
    Disjoint (routeStrip S.first) (routeStrip S.second) := by
  exact graph.routeStrips_disjoint small_faces a _ (T.openEdgeTarget_injective edge)
    (fun t => T.open_edge_cut edge _ (T.openEdgeTarget_inside edge t))
    S.first S.second S.first_member S.second_member S.distinct

include graph small_faces in
/-- The two strips cover exactly the noncut region with endpoints in this open tree edge. -/
theorem cut_edge_strips_iff_endpoint (a : frontier P.body) (T : P.CutLocusTree a)
    {u v : T.vertices} (edge : T.graph.Adj u v) (S : CutEdgeStrips T edge)
    (b : frontier P.body) (different : b ≠ a) :
    b ∈ routeStrip S.first ∪ routeStrip S.second ↔ b ∉ P.cutSet a ∧
      ((graph.cutEndpoint small_faces a ⟨b, different⟩).val : Space) ∈
        openSegment ℝ (u : Space) (v : Space) := by
  rw [graph.routeStrips_iff_endpoint small_faces a _
    (fun t => T.open_edge_cut edge _ (T.openEdgeTarget_inside edge t)) S.first S.second S.fiber,
    T.mem_range_openEdgeTarget]

include graph small_faces in
/-- Strips over distinct unoriented tree edges have disjoint interiors. -/
theorem distinct_cut_edge_strips_disjoint (a : frontier P.body) (T : P.CutLocusTree a)
    {u v w z : T.vertices} (edge : T.graph.Adj u v) (other : T.graph.Adj w z)
    (different_edges : ¬ ((u = w ∧ v = z) ∨ (u = z ∧ v = w)))
    (S : CutEdgeStrips T edge) (R : CutEdgeStrips T other) :
    Disjoint (routeStrip S.first ∪ routeStrip S.second) (routeStrip R.first ∪ routeStrip R.second) := by
  apply disjoint_left.mpr
  intro b first second
  have different : b ≠ a := by
    rcases first with first | first
    · exact (graph.routeStrip_outside_cutSet small_faces a _
        (fun t => T.open_edge_cut edge _ (T.openEdgeTarget_inside edge t)) S.first S.first_member b first).1
    · exact (graph.routeStrip_outside_cutSet small_faces a _
        (fun t => T.open_edge_cut edge _ (T.openEdgeTarget_inside edge t)) S.second S.second_member b first).1
  have inside := (graph.cut_edge_strips_iff_endpoint small_faces a T edge S b different).mp first
  have other_inside := (graph.cut_edge_strips_iff_endpoint small_faces a T other R b different).mp second
  exact different_edges (T.open_edges_meet u v w z edge other _ inside.2 other_inside.2)

end SixVertexGraph
end SixVertexUnfolding.ConvexPolyhedron
