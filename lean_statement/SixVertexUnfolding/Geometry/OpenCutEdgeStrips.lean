import SixVertexUnfolding.Geometry.EmbeddedOpenEdges
import SixVertexUnfolding.Geometry.ClosedCutEdgeRoutes
import SixVertexUnfolding.Geometry.ClosedRouteStrips
import SixVertexUnfolding.Geometry.ClosedStripFibers

/-! The route strips are open subsets of the actual surface. The endpoint
map makes each pair open; the two closed branch extensions separate its sides. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

namespace CutEdgeStrips

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a}
  {u v : T.vertices} {edge : T.graph.Adj u v}

/-- Exchange the two actual route labels. -/
def swap (S : CutEdgeStrips T edge) : CutEdgeStrips T edge where
  first := S.second
  second := S.first
  distinct t := (S.distinct t).symm
  fiber t := (S.fiber t).trans (pair_comm _ _)

end CutEdgeStrips

namespace SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- The union of the two strips over an open tree edge is open on the boundary. -/
theorem cut_edge_strip_pair_open (a : frontier P.body) (T : P.CutLocusTree a)
    {u v : T.vertices} (edge : T.graph.Adj u v) (S : CutEdgeStrips T edge) :
    IsOpen (routeStrip S.first ∪ routeStrip S.second) := by
  let good : Set {b : frontier P.body // b ≠ a} := {b | b.val ∉ P.cutSet a ∧
    ((graph.cutEndpoint small_faces a b).val : Space) ∈ openSegment ℝ (u : Space) (v : Space)}
  have open_good : IsOpen good :=
    ((graph.cutSet_closed small_faces a).isOpen_compl.preimage continuous_subtype_val).inter
      ((T.toEmbeddedCutGraph.open_edge_isOpen edge).preimage (graph.cutEndpoint_continuous small_faces a))
  have equality : Subtype.val '' good = routeStrip S.first ∪ routeStrip S.second := by
    ext b
    constructor
    · rintro ⟨x, inside, rfl⟩
      exact (graph.cut_edge_strips_iff_endpoint small_faces a T edge S x.val x.property).mpr inside
    · intro inside
      have different : b ≠ a := by
        rcases inside with first | second
        · exact (graph.routeStrip_outside_cutSet small_faces a _
            (fun t => T.open_edge_cut edge _ (T.openEdgeTarget_inside edge t)) S.first S.first_member b first).1
        · exact (graph.routeStrip_outside_cutSet small_faces a _
            (fun t => T.open_edge_cut edge _ (T.openEdgeTarget_inside edge t)) S.second S.second_member b second).1
      exact ⟨⟨b, different⟩, (graph.cut_edge_strips_iff_endpoint small_faces a T edge S b different).mp inside, rfl⟩
  rw [← equality]
  exact (isOpen_ne : IsOpen {b : frontier P.body | b ≠ a}).isOpenMap_subtype_val good open_good

include graph small_faces in
/-- A strip does not meet even the closure of its opposite branch. -/
theorem first_strip_disjoint_second_closure (a : frontier P.body) (T : P.CutLocusTree a)
    {u v : T.vertices} (edge : T.graph.Adj u v) (S : CutEdgeStrips T edge) :
    Disjoint (routeStrip S.first) (closure (routeStrip S.second)) := by
  obtain ⟨closed, agrees, member⟩ := graph.cut_edge_route_extension small_faces a T edge S.second S.second_member
  rw [closure_routeStrip_eq S.second closed agrees]
  apply disjoint_left.mpr
  rintro b ⟨⟨x, s⟩, rfl⟩ ⟨⟨y, t⟩, meet⟩
  have equal := graph.cut_rays_meeting small_faces a (T.openEdgeTarget edge x) (T.closedEdgeTarget edge y)
    (T.open_edge_cut edge _ (T.openEdgeTarget_inside edge x)) (T.closedEdgeTarget_cut edge y)
    (S.first x) (closed y) (S.first_member x) (member y) (interiorTime s) t
    s.property.1 s.property.2 meet.symm
  have parameters : interiorTime x = y := T.closedEdgeTarget_injective edge equal.1
  have same : S.first x = S.second x := equal.2.2.trans (by rw [← parameters, agrees])
  exact S.distinct x same

include graph small_faces in
/-- The first branch is itself open on the actual surface. -/
theorem cut_edge_first_strip_open (a : frontier P.body) (T : P.CutLocusTree a)
    {u v : T.vertices} (edge : T.graph.Adj u v) (S : CutEdgeStrips T edge) : IsOpen (routeStrip S.first) := by
  have disjoint := graph.first_strip_disjoint_second_closure small_faces a T edge S
  have equality : routeStrip S.first = (routeStrip S.first ∪ routeStrip S.second) \ closure (routeStrip S.second) := by
    ext b
    constructor
    · intro inside
      exact ⟨Or.inl inside, fun other => disjoint_left.mp disjoint inside other⟩
    · rintro ⟨first | second, outside⟩
      · exact first
      · exact (outside (subset_closure second)).elim
  rw [equality]
  exact (graph.cut_edge_strip_pair_open small_faces a T edge S).sdiff isClosed_closure

include graph small_faces in
/-- Both radial strip interiors are open subsets of the original polyhedral surface. -/
theorem cut_edge_strips_open (a : frontier P.body) (T : P.CutLocusTree a)
    {u v : T.vertices} (edge : T.graph.Adj u v) (S : CutEdgeStrips T edge) :
    IsOpen (routeStrip S.first) ∧ IsOpen (routeStrip S.second) :=
  ⟨graph.cut_edge_first_strip_open small_faces a T edge S,
    graph.cut_edge_first_strip_open small_faces a T edge S.swap⟩

end SixVertexGraph
end SixVertexUnfolding.ConvexPolyhedron
