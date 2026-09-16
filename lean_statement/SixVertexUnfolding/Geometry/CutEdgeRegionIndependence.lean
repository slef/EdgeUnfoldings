import SixVertexUnfolding.Geometry.CutEdgeTriangles

/-! The paired surface region depends only on the unoriented tree edge,
not on branch labels, metric coordinates, or the chosen orientation. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- Matching actual open edges give matching closed paired regions. -/
theorem cut_edge_regions_eq (a : frontier P.body) (T : P.CutLocusTree a)
    {u v w z : T.vertices} {edge : T.graph.Adj u v} {other : T.graph.Adj w z}
    (D : CutEdgeTriangles T edge) (E : CutEdgeTriangles T other)
    (same_edge : openSegment ℝ (u : Space) (v : Space) = openSegment ℝ (w : Space) (z : Space)) :
    D.region = E.region := by
  have not_source {s t : T.vertices} {adj : T.graph.Adj s t}
      (R : CutEdgeStrips T adj) (b : frontier P.body)
      (inside : b ∈ routeStrip R.first ∪ routeStrip R.second) : b ≠ a := by
    rcases inside with first | second
    · exact (graph.routeStrip_outside_cutSet small_faces a _
        (fun x => T.open_edge_cut adj _ (T.openEdgeTarget_inside adj x)) R.first R.first_member b first).1
    · exact (graph.routeStrip_outside_cutSet small_faces a _
        (fun x => T.open_edge_cut adj _ (T.openEdgeTarget_inside adj x)) R.second R.second_member b second).1
  rw [D.region_eq_closure, E.region_eq_closure]
  congr 1
  ext b
  constructor
  · intro inside
    have different := not_source D.strips b inside
    rw [graph.cut_edge_strips_iff_endpoint small_faces a T edge D.strips b different, same_edge] at inside
    exact (graph.cut_edge_strips_iff_endpoint small_faces a T other E.strips b different).mpr inside
  · intro inside
    have different := not_source E.strips b inside
    rw [graph.cut_edge_strips_iff_endpoint small_faces a T other E.strips b different, ← same_edge] at inside
    exact (graph.cut_edge_strips_iff_endpoint small_faces a T edge D.strips b different).mpr inside

include graph small_faces in
theorem reverse_cut_edge_regions (a : frontier P.body) (T : P.CutLocusTree a)
    {u v : T.vertices} {edge : T.graph.Adj u v}
    (D : CutEdgeTriangles T edge) (E : CutEdgeTriangles T edge.symm) : D.region = E.region :=
  graph.cut_edge_regions_eq small_faces a T D E (openSegment_symm ℝ _ _)

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
