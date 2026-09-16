import SixVertexUnfolding.Geometry.StarCutEndpoints
import SixVertexUnfolding.Geometry.StarBoundaryDescription

/-! Exact cut tests in the radial coordinates of each actual triangle. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

namespace CutLocusTree

/-- Only original endpoints of a tree edge can be original vertices. -/
theorem edge_target_original_iff {P : ConvexPolyhedron} {a : frontier P.body}
    (T : P.CutLocusTree a) {u v : T.vertices} (edge : T.graph.Adj u v) (s : unitInterval) :
    (T.closedEdgeTarget edge s : Space) ∈ P.vertices ↔
      (s = 0 ∧ (u : Space) ∈ P.vertices) ∨ (s = 1 ∧ (v : Space) ∈ P.vertices) := by
  by_cases zero : s = 0
  · subst s
    simp only [T.closedEdgeTarget_zero, vertexTarget, Subtype.coe_mk, true_and, zero_ne_one, false_and, or_false]
  by_cases one : s = 1
  · subst s
    simp only [T.closedEdgeTarget_one, vertexTarget, Subtype.coe_mk, one_ne_zero, false_and, true_and, false_or]
  have positive : 0 < (s : ℝ) := lt_of_le_of_ne s.property.1 (fun h => zero (Subtype.ext h.symm))
  have before : (s : ℝ) < 1 := lt_of_le_of_ne s.property.2 (fun h => one (Subtype.ext h))
  have nonvertex := T.openEdgeTarget_nonvertex edge ⟨s, positive, before⟩
  change (T.closedEdgeTarget edge s : Space) ∉ P.vertices at nonvertex
  simp only [nonvertex, zero, one, false_and, or_self]

end CutLocusTree

namespace SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces

/-- A terminal ray is cut precisely at its source, or throughout when its target is original. -/
theorem terminal_ray_cut_iff (a b : frontier P.body)
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val)
    (cut : b ∈ P.cutSet a) (route : P.BoundaryCurve) (member : route ∈ P.geodesicFiber a b)
    (t : unitInterval) : route t ∈ P.starCuts a ↔ t = 0 ∨ (b : Space) ∈ P.vertices := by
  by_cases zero : t = 0
  · subst t
    have at_source : route 0 = a := congrArg Prod.fst member.2
    simp only [at_source, P.source_mem_starCuts a, true_or]
  have positive : 0 < t := lt_of_le_of_ne t.property.1 (Ne.symm zero)
  obtain ⟨different, endpoint⟩ := graph.cutEndpoint_on_route small_faces a b cut route member t positive
  have original := graph.cutEndpoint_original_iff_starCut small_faces a cofacial ⟨route t, different⟩
  rw [endpoint] at original
  simpa only [zero, false_or] using original.symm

/-- The cut part of a triangle is its apex and the full sides ending at original vertices. -/
theorem triangle_ray_cut_iff {a : frontier P.body} {T : P.CutLocusTree a}
    {u v : T.vertices} {edge : T.graph.Adj u v} (D : PlacedCutEdgeTriangles T edge)
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val)
    (side : Bool) (s t : unitInterval) :
    D.routes side s t ∈ P.starCuts a ↔ t = 0 ∨
      (s = 0 ∧ (u : Space) ∈ P.vertices) ∨ (s = 1 ∧ (v : Space) ∈ P.vertices) := by
  rw [graph.terminal_ray_cut_iff small_faces a (T.closedEdgeTarget edge s) cofacial
    (T.closedEdgeTarget_cut edge s) (D.routes side s) (D.routes_member side s) t,
    T.edge_target_original_iff edge s]

end SixVertexGraph
end SixVertexUnfolding.ConvexPolyhedron
