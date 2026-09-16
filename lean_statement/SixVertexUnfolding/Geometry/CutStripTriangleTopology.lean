import SixVertexUnfolding.Geometry.CutEdgeMetricModel
import SixVertexUnfolding.Geometry.ClosedStripFibers
import SixVertexUnfolding.Geometry.TriangleFanParameters
import SixVertexUnfolding.Geometry.EqualFibersHomeomorph

/-! A closed surface strip is homeomorphic to its nondegenerate planar
metric triangle by the actual radial parameters. This proves its topology;
local preservation of all face distances is a separate geometric obligation. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- The radial correspondence uses any specified nondegenerate triangle. -/
theorem closed_strip_triangle_homeomorph_of_noncollinear
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
      (graph.closed_strip_fibers small_faces a T edge routes member x y).trans
        (triangleFan_fibers p l r noncollinear x y).symm)
  let triangle := Homeomorph.setCongr (triangleFan_range p l r)
  refine ⟨H.trans triangle, ?_⟩
  intro z
  exact congrArg Subtype.val (agrees z)

include graph small_faces in
/-- The surface triangle and planar triangle identify exactly the same radial parameters. -/
theorem closed_strip_triangle_homeomorph (a : frontier P.body) (T : P.CutLocusTree a)
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
  exact graph.closed_strip_triangle_homeomorph_of_noncollinear small_faces a T edge
    M.first M.left M.right noncollinear routes member

include graph small_faces in
/-- Every open-edge route strip has the topology of a nondegenerate closed triangle after closure. -/
theorem route_strip_closure_triangle (a : frontier P.body) (T : P.CutLocusTree a)
    {u v : T.vertices} (edge : T.graph.Adj u v)
    (routes : C(Ioo (0 : ℝ) 1, P.BoundaryCurve))
    (member : ∀ t, routes t ∈ P.geodesicFiber a (T.openEdgeTarget edge t)) :
    ∃ p l r : Plane, ¬ Collinear ℝ ({p, l, r} : Set Plane) ∧
      Nonempty (closure (routeStrip routes) ≃ₜ convexHull ℝ ({p, l, r} : Set Plane)) := by
  obtain ⟨closed_routes, agrees, closed_member⟩ := graph.cut_edge_route_extension small_faces a T edge routes member
  obtain ⟨M⟩ := graph.exists_cut_edge_metric_model small_faces a T edge
  obtain ⟨H, _⟩ := graph.closed_strip_triangle_homeomorph small_faces a T edge M closed_routes closed_member
  exact ⟨M.first, M.left, M.right, M.noncollinear.1,
    ⟨(Homeomorph.setCongr (closure_routeStrip_eq routes closed_routes agrees)).trans H⟩⟩

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
