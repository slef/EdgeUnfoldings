import SixVertexUnfolding.Geometry.StarTriangleImage

/-! The closure of the developed star region is exactly the finite
union of its actual closed kites. This identifies its polygonal extent,
including all limiting boundary points. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

namespace CutTreeCharts

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a} (charts : CutTreeCharts T)

/-- The complete finite union of closed polygons in the chosen global plane. -/
def closedImage : Set Plane := ⋃ d : T.graph.Dart, charts.kite d.adj

theorem closedImage_compact : IsCompact charts.closedImage := by
  classical
  letI : Fintype T.vertices := T.finite_vertices.fintype
  letI : DecidableRel T.graph.Adj := Classical.decRel _
  have triangle (p l r : Plane) : IsCompact (convexHull ℝ ({p, l, r} : Set Plane)) :=
    (show ({p, l, r} : Set Plane).Finite by simp).isCompact_convexHull ℝ
  exact isCompact_iUnion (fun d : T.graph.Dart => (triangle _ _ _).union (triangle _ _ _))

theorem develop_range_subset_closedImage :
    range (fun b : P.UncutSurface a => charts.develop b.val) ⊆ charts.closedImage := by
  rintro _ ⟨b, rfl⟩
  obtain ⟨u, v, edge, placed⟩ := charts.develop_spec b.val
  exact mem_iUnion.mpr ⟨(⟨(u, v), edge⟩ : T.graph.Dart), (charts.global edge).places_mem_kite placed⟩

end CutTreeCharts

namespace SixVertexGraph

/-- No part of a kite is extraneous: each closed triangle is the limit of actual developed points. -/
theorem closure_develop_range_eq_closedImage {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
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
      exact closure_mono (graph.triangle_interior_subset_develop_range small_faces charts cofacial d.adj side)
    intro x member
    obtain ⟨d, member⟩ := mem_iUnion.mp member
    rcases member with first | second
    · exact side_in d false first
    · exact side_in d true second

end SixVertexGraph
end SixVertexUnfolding.ConvexPolyhedron
