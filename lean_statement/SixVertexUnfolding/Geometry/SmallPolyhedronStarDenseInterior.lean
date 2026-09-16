import SixVertexUnfolding.Geometry.StarDenseInterior
import SixVertexUnfolding.Geometry.SmallPolyhedronGlobalTriangleInterior
import SixVertexUnfolding.Geometry.SmallPolyhedronCutTreeStripDensity
import SixVertexUnfolding.Geometry.SmallPolyhedronCutTreeRadialPartition

/-! Interior triangle points form a dense subset of the retained
surface. At every such point the global development is already injective.
This version uses the broader small-polyhedron route results. Where
nonoverlap is needed, it is stated explicitly as separation of the charts. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set Filter Topology

variable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include size small_faces

theorem small_triangle_interior_points_dense {a : frontier P.body} {T : P.CutLocusTree a}
    (charts : CutTreeCharts T) : Dense charts.triangleInteriorPoints := by
  have dense := (small_cut_tree_strip_points_dense size small_faces a T).preimage
    ((P.starCuts_closed a).isOpen_compl.isOpenMap_subtype_val)
  apply dense.mono
  intro b good
  obtain source | cut | ray | ⟨u, v, edge, in_strip⟩ := small_cut_tree_radial_partition size small_faces a T
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

theorem small_develop_unique_on_dense_interiors {a : frontier P.body} {T : P.CutLocusTree a}
    (charts : CutTreeCharts T) (separated : charts.KitesSeparated)
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val)
    (b : P.UncutSurface a) (good : b ∈ charts.triangleInteriorPoints)
    (c : P.UncutSurface a) (same : charts.develop b.val = charts.develop c.val) : b = c := by
  obtain ⟨u, v, edge, side, inside, interior_point⟩ := good
  exact small_develop_injective_at_triangle_interior size small_faces charts separated cofacial
    edge side b c inside interior_point same

end SixVertexUnfolding.ConvexPolyhedron
