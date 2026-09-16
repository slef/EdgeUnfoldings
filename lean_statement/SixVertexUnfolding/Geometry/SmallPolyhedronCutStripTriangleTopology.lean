import SixVertexUnfolding.Geometry.CutStripTriangleTopology
import SixVertexUnfolding.Geometry.SmallPolyhedronClosedCutEdgeRoutes
import SixVertexUnfolding.Geometry.SmallPolyhedronClosedStripFibers
import SixVertexUnfolding.Geometry.SmallPolyhedronCutEdgeMetricModel

/-! A closed surface strip is homeomorphic to its nondegenerate planar
metric triangle by the actual radial parameters. This proves its topology;
local preservation of all face distances is a separate geometric obligation.

Here the shortest-route inputs come from the actual vertex fans of a
polyhedron with at most six vertices and triangular/quadrilateral faces.
No canonical graph model is assumed. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

variable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include size small_faces in
/-- The radial correspondence uses any specified nondegenerate triangle. -/
theorem small_closed_strip_triangle_homeomorph_of_noncollinear
    (a : frontier P.body) (T : P.CutLocusTree a)
    {u v : T.vertices} (edge : T.graph.Adj u v) (p l r : Plane)
    (noncollinear : ¬ Collinear ℝ ({l, r, p} : Set Plane))
    (routes : C(unitInterval, P.BoundaryCurve))
    (member : ∀ t, routes t ∈ P.geodesicFiber a (T.closedEdgeTarget edge t)) :
    ∃ H : range (closedRouteStripMap routes) ≃ₜ convexHull ℝ ({p, l, r} : Set Plane),
      ∀ z, (H ⟨closedRouteStripMap routes z, mem_range_self z⟩ : Plane) =
        triangleFanMap p l r z := by
  obtain ⟨H, agrees⟩ := equal_fibers_homeomorph (closedRouteStripMap routes)
    (triangleFanMap p l r) (fun x y =>
      (small_closed_strip_fibers size small_faces a T edge routes member x y).trans
        (triangleFan_fibers p l r noncollinear x y).symm)
  let triangle := Homeomorph.setCongr (triangleFan_range p l r)
  refine ⟨H.trans triangle, ?_⟩
  intro z
  exact congrArg Subtype.val (agrees z)

include size small_faces in
/-- The surface triangle and planar triangle identify exactly the same radial parameters. -/
theorem small_closed_strip_triangle_homeomorph (a : frontier P.body) (T : P.CutLocusTree a)
    {u v : T.vertices} (edge : T.graph.Adj u v) (M : CutEdgeMetricModel T edge)
    (routes : C(unitInterval, P.BoundaryCurve))
    (member : ∀ t, routes t ∈ P.geodesicFiber a (T.closedEdgeTarget edge t)) :
    ∃ H : range (closedRouteStripMap routes) ≃ₜ convexHull ℝ ({M.first, M.left, M.right} : Set Plane),
      ∀ z, (H ⟨closedRouteStripMap routes z, mem_range_self z⟩ : Plane) =
        triangleFanMap M.first M.left M.right z := by
  have noncollinear : ¬ Collinear ℝ ({M.left, M.right, M.first} : Set Plane) := by
    rw [show ({M.left, M.right, M.first} : Set Plane) = {M.first, M.left, M.right} by
      ext x; simp only [mem_insert_iff, mem_singleton_iff]; tauto]
    exact M.noncollinear.1
  exact small_closed_strip_triangle_homeomorph_of_noncollinear size small_faces a T edge
    M.first M.left M.right noncollinear routes member

include size small_faces in
/-- Every open-edge route strip has the topology of a nondegenerate closed triangle after closure. -/
theorem small_route_strip_closure_triangle (a : frontier P.body) (T : P.CutLocusTree a)
    {u v : T.vertices} (edge : T.graph.Adj u v)
    (routes : C(Ioo (0 : ℝ) 1, P.BoundaryCurve))
    (member : ∀ t, routes t ∈ P.geodesicFiber a (T.openEdgeTarget edge t)) :
    ∃ p l r : Plane, ¬ Collinear ℝ ({p, l, r} : Set Plane) ∧
      Nonempty (closure (routeStrip routes) ≃ₜ convexHull ℝ ({p, l, r} : Set Plane)) := by
  obtain ⟨closed_routes, agrees, closed_member⟩ := small_cut_edge_route_extension size small_faces a T edge routes member
  obtain ⟨M⟩ := small_exists_cut_edge_metric_model size small_faces a T edge
  obtain ⟨H, _⟩ := small_closed_strip_triangle_homeomorph size small_faces a T edge M closed_routes closed_member
  exact ⟨M.first, M.left, M.right, M.noncollinear.1,
    ⟨(Homeomorph.setCongr (closure_routeStrip_eq routes closed_routes agrees)).trans H⟩⟩

end SixVertexUnfolding.ConvexPolyhedron
