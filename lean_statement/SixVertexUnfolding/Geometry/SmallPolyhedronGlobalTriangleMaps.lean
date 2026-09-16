import SixVertexUnfolding.Geometry.GlobalTriangleMaps
import SixVertexUnfolding.Geometry.SmallPolyhedronPlacedRayTargets

/-! The actual surface-point placements in the one global plane.
Reversing a tree edge preserves every represented point and ray.
This version uses at most six vertices and triangular/quadrilateral faces,
without a canonical graph assumption. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

variable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include size small_faces

/-- Reversal changes the edge parameter, while preserving the actual surface placement. -/
theorem small_global_ray_placement_reverse {a : frontier P.body} {T : P.CutLocusTree a}
    (charts : CutTreeCharts T) {u v : T.vertices} (edge : T.graph.Adj u v)
    {s : unitInterval} {b : frontier P.body} {x : Plane} (not_source : b ≠ a)
    (placed : (charts.global edge).PlacesOnRay s b x) :
    (charts.global edge.symm).PlacesOnRay (unitInterval.symm s) b x := by
  have reversed := (charts.places_reverse edge b x).mp
    (((charts.global edge).places_iff_ray b x).mpr ⟨s, placed⟩)
  obtain ⟨t, other⟩ := ((charts.global edge.symm).places_iff_ray b x).mp reversed
  have targets := small_placed_ray_targets_equal size small_faces (charts.global edge)
    (charts.global edge.symm) not_source placed other
  have parameter : t = unitInterval.symm s := T.closedEdgeTarget_injective edge.symm
    (targets.symm.trans (T.closedEdgeTarget_reverse edge s).symm)
  rwa [← parameter]

end SixVertexUnfolding.ConvexPolyhedron
