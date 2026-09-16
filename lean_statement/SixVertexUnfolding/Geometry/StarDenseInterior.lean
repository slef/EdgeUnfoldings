import SixVertexUnfolding.Geometry.GlobalTriangleInterior
import SixVertexUnfolding.Geometry.CutTreeStripDensity
import SixVertexUnfolding.Geometry.RadialStripInterior

/-! Interior triangle points form a dense subset of the retained
surface. At every such point the global development is already injective. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

namespace CutEdgeTriangles

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a}
    {u v : T.vertices} {edge : T.graph.Adj u v} (D : CutEdgeTriangles T edge)

def openRoutes : Bool → C(Ioo (0 : ℝ) 1, P.BoundaryCurve)
  | false => D.strips.first
  | true => D.strips.second

theorem routes_agree (side : Bool) (t : Ioo (0 : ℝ) 1) :
    D.routes side (interiorTime t) = D.openRoutes side t := by
  cases side
  · exact (D.agrees t).1
  · exact (D.agrees t).2

end CutEdgeTriangles

namespace CutTreeCharts

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a} (charts : CutTreeCharts T)

def triangleInteriorPoints : Set (P.UncutSurface a) :=
  {b | ∃ u v : T.vertices, ∃ edge : T.graph.Adj u v, ∃ side : Bool,
    ∃ inside : b.val ∈ range (closedRouteStripMap ((charts.global edge).routes side)),
      (((charts.global edge).sideTriangle side).homeomorph ⟨b.val, inside⟩ : Plane) ∈
        interior ((charts.global edge).sideRegion side)}

end CutTreeCharts

namespace SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces

theorem triangle_interior_points_dense {a : frontier P.body} {T : P.CutLocusTree a}
    (charts : CutTreeCharts T) : Dense charts.triangleInteriorPoints := by
  have dense := (graph.cut_tree_strip_points_dense small_faces a T).preimage
    ((P.starCuts_closed a).isOpen_compl.isOpenMap_subtype_val)
  apply dense.mono
  intro b good
  obtain source | cut | ray | ⟨u, v, edge, in_strip⟩ := graph.cut_tree_radial_partition small_faces a T
    (fun _ _ edge => (charts.global edge).strips) b.val
  · exact (good.1 source).elim
  · exact (good.2.1 cut).elim
  · exact (good.2.2 ray).elim
  · have side_exists : ∃ side, b.val ∈ routeStrip ((charts.global edge).openRoutes side) := by
      rcases in_strip with first | second
      · exact ⟨false, first⟩
      · exact ⟨true, second⟩
    obtain ⟨side, strip⟩ := side_exists
    have inside : b.val ∈ range (closedRouteStripMap ((charts.global edge).routes side)) := by
      rw [← closure_routeStrip_eq _ _ ((charts.global edge).routes_agree side)]
      exact subset_closure strip
    refine ⟨u, v, edge, side, inside, ?_⟩
    exact (((charts.global edge).sideTriangle side).interior_iff_open_strip
      ((charts.global edge).side_noncollinear side) ((charts.global edge).openRoutes side)
      ((charts.global edge).routes_agree side) ⟨b.val, inside⟩).mpr strip

theorem develop_unique_on_dense_interiors {a : frontier P.body} {T : P.CutLocusTree a}
    (charts : CutTreeCharts T) (source : Fin 6) (at_source : (a : Space) = (graph.vertex source : Space))
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val)
    (b : P.UncutSurface a) (good : b ∈ charts.triangleInteriorPoints)
    (c : P.UncutSurface a) (same : charts.develop b.val = charts.develop c.val) : b = c := by
  obtain ⟨u, v, edge, side, inside, interior_point⟩ := good
  exact graph.develop_injective_at_triangle_interior small_faces charts source at_source cofacial
    edge side b c inside interior_point same

end SixVertexGraph
end SixVertexUnfolding.ConvexPolyhedron
