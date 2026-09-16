import SixVertexUnfolding.Geometry.StarPolygonClosure
import SixVertexUnfolding.Geometry.SmallPolyhedronStarTriangleImage

/-! The closure of the developed star region is exactly the finite
union of its actual closed kites. This identifies its polygonal extent,
including all limiting boundary points.
This version uses the broader small-polyhedron route results. Where
nonoverlap is needed, it is stated explicitly as separation of the charts. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set Filter Topology

/-- No part of a kite is extraneous: each closed triangle is the limit of actual developed points. -/
theorem small_closure_develop_range_eq_closedImage {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)
    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4)
    {a : frontier P.body} {T : P.CutLocusTree a} (charts : CutTreeCharts T)
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val) :
    closure (range (fun b : P.UncutSurface a => charts.develop b.val)) = charts.closedImage := by
  apply Subset.antisymm
  · exact closure_minimal charts.develop_range_subset_closedImage charts.closedImage_compact.isClosed
  · have side_in (d : T.graph.Dart) (side : Bool) : (charts.global d.adj).sideRegion side ⊆
        closure (range (fun b : P.UncutSurface a => charts.develop b.val)) := by
      rw [← (charts.global d.adj).side_regular side]
      exact closure_mono (small_triangle_interior_subset_develop_range size small_faces charts cofacial d.adj side)
    intro x member
    obtain ⟨d, member⟩ := mem_iUnion.mp member
    rcases member with first | second
    · exact side_in d false first
    · exact side_in d true second

end SixVertexUnfolding.ConvexPolyhedron
