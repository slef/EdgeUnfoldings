import SixVertexUnfolding.Geometry.CutEdgeStrips
import SixVertexUnfolding.Geometry.SmallPolyhedronCutEdgeRouteBranches
import SixVertexUnfolding.Geometry.SmallPolyhedronCutRetraction
import SixVertexUnfolding.Geometry.SmallPolyhedronRouteStripCoverage
import SixVertexUnfolding.Geometry.SmallPolyhedronRouteStrips

/-! The two shortest-route strips attached to an actual open cut-tree edge.
Their parameters are one point of that edge and one interior route time.

Here the shortest-route inputs come from the actual vertex fans of a
polyhedron with at most six vertices and triangular/quadrilateral faces.
No canonical graph model is assumed. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

variable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include size small_faces in
theorem small_exists_cut_edge_strips (a : frontier P.body) (T : P.CutLocusTree a)
    {u v : T.vertices} (edge : T.graph.Adj u v) : Nonempty (CutEdgeStrips T edge) := by
  obtain ⟨first, second, distinct, pair⟩ := small_cut_edge_continuous_routes size small_faces a T edge
  exact ⟨⟨first, second, distinct, pair⟩⟩

include size small_faces in
/-- Each strip is parametrized without identifying distinct points. -/
theorem small_cut_edge_strips_injective (a : frontier P.body) (T : P.CutLocusTree a)
    {u v : T.vertices} (edge : T.graph.Adj u v) (S : CutEdgeStrips T edge) :
    Function.Injective (routeStripMap S.first) ∧ Function.Injective (routeStripMap S.second) := by
  have cut t := T.open_edge_cut edge (T.openEdgeTarget edge t) (T.openEdgeTarget_inside edge t)
  exact ⟨small_routeStripMap_injective size small_faces a _ (T.openEdgeTarget_injective edge)
      cut S.first S.first_member,
    small_routeStripMap_injective size small_faces a _ (T.openEdgeTarget_injective edge)
      cut S.second S.second_member⟩

include size small_faces in
/-- The two sides of the same edge have disjoint swept interiors. -/
theorem small_cut_edge_strips_disjoint (a : frontier P.body) (T : P.CutLocusTree a)
    {u v : T.vertices} (edge : T.graph.Adj u v) (S : CutEdgeStrips T edge) :
    Disjoint (routeStrip S.first) (routeStrip S.second) := by
  exact small_routeStrips_disjoint size small_faces a _ (T.openEdgeTarget_injective edge)
    (fun t => T.open_edge_cut edge _ (T.openEdgeTarget_inside edge t))
    S.first S.second S.first_member S.second_member S.distinct

include size small_faces in
/-- The two strips cover exactly the noncut region with endpoints in this open tree edge. -/
theorem small_cut_edge_strips_iff_endpoint (a : frontier P.body) (T : P.CutLocusTree a)
    {u v : T.vertices} (edge : T.graph.Adj u v) (S : CutEdgeStrips T edge)
    (b : frontier P.body) (different : b ≠ a) :
    b ∈ routeStrip S.first ∪ routeStrip S.second ↔ b ∉ P.cutSet a ∧
      ((small_cutEndpoint size small_faces a ⟨b, different⟩).val : Space) ∈
        openSegment ℝ (u : Space) (v : Space) := by
  rw [small_routeStrips_iff_endpoint size small_faces a _
    (fun t => T.open_edge_cut edge _ (T.openEdgeTarget_inside edge t)) S.first S.second S.fiber,
    T.mem_range_openEdgeTarget]

include size small_faces in
/-- Strips over distinct unoriented tree edges have disjoint interiors. -/
theorem small_distinct_cut_edge_strips_disjoint (a : frontier P.body) (T : P.CutLocusTree a)
    {u v w z : T.vertices} (edge : T.graph.Adj u v) (other : T.graph.Adj w z)
    (different_edges : ¬ ((u = w ∧ v = z) ∨ (u = z ∧ v = w)))
    (S : CutEdgeStrips T edge) (R : CutEdgeStrips T other) :
    Disjoint (routeStrip S.first ∪ routeStrip S.second) (routeStrip R.first ∪ routeStrip R.second) := by
  apply disjoint_left.mpr
  intro b first second
  have different : b ≠ a := by
    rcases first with first | first
    · exact (small_routeStrip_outside_cutSet size small_faces a _
        (fun t => T.open_edge_cut edge _ (T.openEdgeTarget_inside edge t)) S.first S.first_member b first).1
    · exact (small_routeStrip_outside_cutSet size small_faces a _
        (fun t => T.open_edge_cut edge _ (T.openEdgeTarget_inside edge t)) S.second S.second_member b first).1
  have inside := (small_cut_edge_strips_iff_endpoint size small_faces a T edge S b different).mp first
  have other_inside := (small_cut_edge_strips_iff_endpoint size small_faces a T other R b different).mp second
  exact different_edges (T.open_edges_meet u v w z edge other _ inside.2 other_inside.2)

end SixVertexUnfolding.ConvexPolyhedron
