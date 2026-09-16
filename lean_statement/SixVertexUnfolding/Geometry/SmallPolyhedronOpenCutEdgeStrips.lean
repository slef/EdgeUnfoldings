import SixVertexUnfolding.Geometry.OpenCutEdgeStrips
import SixVertexUnfolding.Geometry.SmallPolyhedronClosedCutEdgeRoutes
import SixVertexUnfolding.Geometry.SmallPolyhedronCutEdgeStrips
import SixVertexUnfolding.Geometry.SmallPolyhedronCutRayCoordinates
import SixVertexUnfolding.Geometry.SmallPolyhedronCutRetraction
import SixVertexUnfolding.Geometry.SmallPolyhedronRouteStability
import SixVertexUnfolding.Geometry.SmallPolyhedronRouteStrips

/-! The route strips are open subsets of the actual surface. The endpoint
map makes each pair open; the two closed branch extensions separate its sides.

Here the shortest-route inputs come from the actual vertex fans of a
polyhedron with at most six vertices and triangular/quadrilateral faces.
No canonical graph model is assumed. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

variable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include size small_faces in
/-- The union of the two strips over an open tree edge is open on the boundary. -/
theorem small_cut_edge_strip_pair_open (a : frontier P.body) (T : P.CutLocusTree a)
    {u v : T.vertices} (edge : T.graph.Adj u v) (S : CutEdgeStrips T edge) :
    IsOpen (routeStrip S.first ∪ routeStrip S.second) := by
  let good : Set {b : frontier P.body // b ≠ a} := {b | b.val ∉ P.cutSet a ∧
    ((small_cutEndpoint size small_faces a b).val : Space) ∈ openSegment ℝ (u : Space) (v : Space)}
  have open_good : IsOpen good :=
    ((small_cutSet_closed size small_faces a).isOpen_compl.preimage continuous_subtype_val).inter
      ((T.toEmbeddedCutGraph.open_edge_isOpen edge).preimage (small_cutEndpoint_continuous size small_faces a))
  have equality : Subtype.val '' good = routeStrip S.first ∪ routeStrip S.second := by
    ext b
    constructor
    · rintro ⟨x, inside, rfl⟩
      exact (small_cut_edge_strips_iff_endpoint size small_faces a T edge S x.val x.property).mpr inside
    · intro inside
      have different : b ≠ a := by
        rcases inside with first | second
        · exact (small_routeStrip_outside_cutSet size small_faces a _
            (fun t => T.open_edge_cut edge _ (T.openEdgeTarget_inside edge t)) S.first S.first_member b first).1
        · exact (small_routeStrip_outside_cutSet size small_faces a _
            (fun t => T.open_edge_cut edge _ (T.openEdgeTarget_inside edge t)) S.second S.second_member b second).1
      exact ⟨⟨b, different⟩, (small_cut_edge_strips_iff_endpoint size small_faces a T edge S b different).mp inside, rfl⟩
  rw [← equality]
  exact (isOpen_ne : IsOpen {b : frontier P.body | b ≠ a}).isOpenMap_subtype_val good open_good

include size small_faces in
/-- A strip does not meet even the closure of its opposite branch. -/
theorem small_first_strip_disjoint_second_closure (a : frontier P.body) (T : P.CutLocusTree a)
    {u v : T.vertices} (edge : T.graph.Adj u v) (S : CutEdgeStrips T edge) :
    Disjoint (routeStrip S.first) (closure (routeStrip S.second)) := by
  obtain ⟨closed, agrees, member⟩ := small_cut_edge_route_extension size small_faces a T edge S.second S.second_member
  rw [closure_routeStrip_eq S.second closed agrees]
  apply disjoint_left.mpr
  rintro b ⟨⟨x, s⟩, rfl⟩ ⟨⟨y, t⟩, meet⟩
  have equal := small_cut_rays_meeting size small_faces a (T.openEdgeTarget edge x) (T.closedEdgeTarget edge y)
    (T.open_edge_cut edge _ (T.openEdgeTarget_inside edge x)) (T.closedEdgeTarget_cut edge y)
    (S.first x) (closed y) (S.first_member x) (member y) (interiorTime s) t
    s.property.1 s.property.2 meet.symm
  have parameters : interiorTime x = y := T.closedEdgeTarget_injective edge equal.1
  have same : S.first x = S.second x := equal.2.2.trans (by rw [← parameters, agrees])
  exact S.distinct x same

include size small_faces in
/-- The first branch is itself open on the actual surface. -/
theorem small_cut_edge_first_strip_open (a : frontier P.body) (T : P.CutLocusTree a)
    {u v : T.vertices} (edge : T.graph.Adj u v) (S : CutEdgeStrips T edge) : IsOpen (routeStrip S.first) := by
  have disjoint := small_first_strip_disjoint_second_closure size small_faces a T edge S
  have equality : routeStrip S.first = (routeStrip S.first ∪ routeStrip S.second) \ closure (routeStrip S.second) := by
    ext b
    constructor
    · intro inside
      exact ⟨Or.inl inside, fun other => disjoint_left.mp disjoint inside other⟩
    · rintro ⟨first | second, outside⟩
      · exact first
      · exact (outside (subset_closure second)).elim
  rw [equality]
  exact (small_cut_edge_strip_pair_open size small_faces a T edge S).sdiff isClosed_closure

include size small_faces in
/-- Both radial strip interiors are open subsets of the original polyhedral surface. -/
theorem small_cut_edge_strips_open (a : frontier P.body) (T : P.CutLocusTree a)
    {u v : T.vertices} (edge : T.graph.Adj u v) (S : CutEdgeStrips T edge) :
    IsOpen (routeStrip S.first) ∧ IsOpen (routeStrip S.second) :=
  ⟨small_cut_edge_first_strip_open size small_faces a T edge S,
    small_cut_edge_first_strip_open size small_faces a T edge S.swap⟩

end SixVertexUnfolding.ConvexPolyhedron
