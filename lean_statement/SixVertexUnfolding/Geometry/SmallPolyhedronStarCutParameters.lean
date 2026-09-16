import SixVertexUnfolding.Geometry.StarCutParameters
import SixVertexUnfolding.Geometry.SmallPolyhedronStarCutEndpoints
import SixVertexUnfolding.Geometry.SmallPolyhedronStarBoundaryDescription

/-! Exact cut tests in the radial coordinates of each actual triangle.
This version uses the broader small-polyhedron route results. Where
nonoverlap is needed, it is stated explicitly as separation of the charts. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set Filter Topology

variable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include size small_faces

/-- A terminal ray is cut precisely at its source, or throughout when its target is original. -/
theorem small_terminal_ray_cut_iff (a b : frontier P.body)
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val)
    (cut : b ∈ P.cutSet a) (route : P.BoundaryCurve) (member : route ∈ P.geodesicFiber a b)
    (t : unitInterval) : route t ∈ P.starCuts a ↔ t = 0 ∨ (b : Space) ∈ P.vertices := by
  by_cases zero : t = 0
  · subst t
    have at_source : route 0 = a := congrArg Prod.fst member.2
    simp only [at_source, P.source_mem_starCuts a, true_or]
  have positive : 0 < t := lt_of_le_of_ne t.property.1 (Ne.symm zero)
  obtain ⟨different, endpoint⟩ := small_cutEndpoint_on_route size small_faces a b cut route member t positive
  have original := small_cutEndpoint_original_iff_starCut size small_faces a cofacial ⟨route t, different⟩
  rw [endpoint] at original
  simpa only [zero, false_or] using original.symm

/-- The cut part of a triangle is its apex and the full sides ending at original vertices. -/
theorem small_triangle_ray_cut_iff {a : frontier P.body} {T : P.CutLocusTree a}
    {u v : T.vertices} {edge : T.graph.Adj u v} (D : PlacedCutEdgeTriangles T edge)
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val)
    (side : Bool) (s t : unitInterval) :
    D.routes side s t ∈ P.starCuts a ↔ t = 0 ∨
      (s = 0 ∧ (u : Space) ∈ P.vertices) ∨ (s = 1 ∧ (v : Space) ∈ P.vertices) := by
  rw [small_terminal_ray_cut_iff size small_faces a (T.closedEdgeTarget edge s) cofacial
    (T.closedEdgeTarget_cut edge s) (D.routes side s) (D.routes_member side s) t,
    T.edge_target_original_iff edge s]

end SixVertexUnfolding.ConvexPolyhedron
