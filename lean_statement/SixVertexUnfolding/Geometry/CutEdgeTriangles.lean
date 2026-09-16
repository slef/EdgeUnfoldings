import SixVertexUnfolding.Geometry.CutEdgeTriangleDevelopments

/-! Keep the two actual radial developments of a cut edge together.
All fields are supplied by the existing geometric constructions. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- The two closed strips, their metric kite, and their actual triangle developments. -/
structure CutEdgeTriangles {P : ConvexPolyhedron} {a : frontier P.body}
    (T : P.CutLocusTree a) {u v : T.vertices} (edge : T.graph.Adj u v) where
  strips : CutEdgeStrips T edge
  model : CutEdgeMetricModel T edge
  first : C(unitInterval, P.BoundaryCurve)
  second : C(unitInterval, P.BoundaryCurve)
  agrees : ∀ t, first (interiorTime t) = strips.first t ∧ second (interiorTime t) = strips.second t
  member : ∀ t, first t ∈ P.geodesicFiber a (T.closedEdgeTarget edge t) ∧
    second t ∈ P.geodesicFiber a (T.closedEdgeTarget edge t)
  first_triangle : RadialStripTriangle first model.first model.left model.right
  second_triangle : RadialStripTriangle second model.second model.left model.right

namespace CutEdgeTriangles

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a}
  {u v : T.vertices} {edge : T.graph.Adj u v} (D : CutEdgeTriangles T edge)

/-- The actual surface region swept by the two closed route families. -/
def region : Set (frontier P.body) :=
  range (closedRouteStripMap D.first) ∪ range (closedRouteStripMap D.second)

theorem region_closed : IsClosed D.region :=
  (isCompact_range (closedRouteStripMap D.first).continuous).isClosed.union
    (isCompact_range (closedRouteStripMap D.second).continuous).isClosed

theorem region_eq_closure : D.region = closure (routeStrip D.strips.first ∪ routeStrip D.strips.second) := by
  rw [closure_union, closure_routeStrip_eq _ _ (fun t => (D.agrees t).1),
    closure_routeStrip_eq _ _ (fun t => (D.agrees t).2)]
  rfl

end CutEdgeTriangles

namespace SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- Both complete radial triangles exist for every actual cut-tree edge. -/
theorem exists_cut_edge_triangles (a : frontier P.body) (T : P.CutLocusTree a)
    {u v : T.vertices} (edge : T.graph.Adj u v) : Nonempty (CutEdgeTriangles T edge) := by
  obtain ⟨strips⟩ := graph.exists_cut_edge_strips small_faces a T edge
  obtain ⟨model, first, second, agrees, member, ⟨D⟩, ⟨E⟩⟩ :=
    graph.exists_cut_edge_triangle_developments small_faces a T edge strips
  exact ⟨⟨strips, model, first, second, agrees, member, D, E⟩⟩

end SixVertexGraph
end SixVertexUnfolding.ConvexPolyhedron
