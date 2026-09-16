import SixVertexUnfolding.Geometry.PlacedRayTargets

/-! The actual surface-point placements in the one global plane.
Reversing a tree edge preserves every represented point and ray. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

namespace CutTreeCharts

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a} (charts : CutTreeCharts T)

noncomputable def global {u v : T.vertices} (edge : T.graph.Adj u v) : PlacedCutEdgeTriangles T edge :=
  (charts.triangles edge).inFrame (charts.frames.frame u)

theorem places_reverse {u v : T.vertices} (edge : T.graph.Adj u v) (b : frontier P.body) (x : Plane) :
    (charts.global edge).Places b x ↔ (charts.global edge.symm).Places b x := by
  constructor
  · intro placed
    exact (charts.frames.global_reversal edge).2.2.places placed
  · intro placed
    exact (charts.frames.global_reversal edge.symm).2.2.places placed

theorem exists_global_placement (b : frontier P.body) :
    ∃ u v : T.vertices, ∃ edge : T.graph.Adj u v, ∃ x : Plane, (charts.global edge).Places b x := by
  obtain ⟨u, v, edge, covered⟩ := charts.covers b
  exact ⟨u, v, edge, ((charts.global edge).exists_placement_iff b).mpr covered⟩

end CutTreeCharts

namespace SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces

/-- Reversal changes the edge parameter, while preserving the actual surface placement. -/
theorem global_ray_placement_reverse {a : frontier P.body} {T : P.CutLocusTree a}
    (charts : CutTreeCharts T) {u v : T.vertices} (edge : T.graph.Adj u v)
    {s : unitInterval} {b : frontier P.body} {x : Plane} (not_source : b ≠ a)
    (placed : (charts.global edge).PlacesOnRay s b x) :
    (charts.global edge.symm).PlacesOnRay (unitInterval.symm s) b x := by
  have reversed := (charts.places_reverse edge b x).mp
    (((charts.global edge).places_iff_ray b x).mpr ⟨s, placed⟩)
  obtain ⟨t, other⟩ := ((charts.global edge.symm).places_iff_ray b x).mp reversed
  have targets := graph.placed_ray_targets_equal small_faces (charts.global edge)
    (charts.global edge.symm) not_source placed other
  have parameter : t = unitInterval.symm s := T.closedEdgeTarget_injective edge.symm
    (targets.symm.trans (T.closedEdgeTarget_reverse edge s).symm)
  rwa [← parameter]

end SixVertexGraph
end SixVertexUnfolding.ConvexPolyhedron
