import SixVertexUnfolding.Geometry.StarDevelopmentMap
import SixVertexUnfolding.Geometry.PlacedTriangleGeometry

/-! The entire development lies in a finite union of compact actual kites. -/

namespace SixVertexUnfolding.ConvexPolyhedron.CutTreeCharts

open Set

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a} (charts : CutTreeCharts T)

theorem develop_range_bounded :
    Bornology.IsBounded (range (fun b : P.UncutSurface a => charts.develop b.val)) := by
  classical
  letI : Fintype T.vertices := T.finite_vertices.fintype
  letI : DecidableRel T.graph.Adj := Classical.decRel _
  have compact_triangle (p l r : Plane) : IsCompact (convexHull ℝ ({p, l, r} : Set Plane)) := by
    have finite : ({p, l, r} : Set Plane).Finite := by simp
    exact finite.isCompact_convexHull ℝ
  have compact_kite (d : T.graph.Dart) : IsCompact (charts.kite d.adj) := by
    exact (compact_triangle _ _ _).union (compact_triangle _ _ _)
  have bounded := (isCompact_iUnion compact_kite).isBounded
  apply bounded.subset
  rintro x ⟨b, rfl⟩
  obtain ⟨u, v, edge, placed⟩ := charts.develop_spec b.val
  exact mem_iUnion.mpr ⟨(⟨(u, v), edge⟩ : T.graph.Dart), (charts.global edge).places_mem_kite placed⟩

end SixVertexUnfolding.ConvexPolyhedron.CutTreeCharts
