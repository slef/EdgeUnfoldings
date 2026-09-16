import SixVertexUnfolding.Geometry.GlobalTriangleMaps
import SixVertexUnfolding.Geometry.EmbeddedEdgeIntersections

/-! Incidence of the actual embedded tree, expressed in the closed
edge parameters retained by the radial triangle maps. -/

namespace SixVertexUnfolding.ConvexPolyhedron.CutLocusTree

open Set

variable {P : ConvexPolyhedron} {a : frontier P.body} (T : P.CutLocusTree a)

theorem closedEdgeTarget_in_segment {u v : T.vertices} (edge : T.graph.Adj u v) (s : unitInterval) :
    (T.closedEdgeTarget edge s : Space) ∈ segment ℝ (u : Space) (v : Space) := by
  rw [segment_eq_image_lineMap]
  exact ⟨s, s.property, rfl⟩

/-- A graph vertex occurs on a closed edge only at parameter zero or one. -/
theorem parameter_endpoint_of_vertex {u v w : T.vertices} (edge : T.graph.Adj u v) (s : unitInterval)
    (at_vertex : T.closedEdgeTarget edge s = T.vertexTarget w) : s = 0 ∨ s = 1 := by
  have on_segment : (w : Space) ∈ segment ℝ (u : Space) (v : Space) := by
    simpa only [at_vertex] using T.closedEdgeTarget_in_segment edge s
  rcases T.toEmbeddedCutGraph.vertex_on_edge edge on_segment with rfl | rfl
  · exact Or.inl (T.closedEdgeTarget_injective edge (at_vertex.trans (T.closedEdgeTarget_zero edge).symm))
  · exact Or.inr (T.closedEdgeTarget_injective edge (at_vertex.trans (T.closedEdgeTarget_one edge).symm))

/-- If a second closed edge meets the interior of the first, it is the same unoriented edge. -/
theorem same_edge_of_interior_target {u v w z : T.vertices} (first : T.graph.Adj u v)
    (second : T.graph.Adj w z) {s t : unitInterval} (positive : 0 < s) (before : s < 1)
    (targets : T.closedEdgeTarget first s = T.closedEdgeTarget second t) : s(u, v) = s(w, z) := by
  by_contra different
  have distinct : ¬ ((u = w ∧ v = z) ∨ (u = z ∧ v = w)) := fun same => different (Sym2.eq_iff.mpr same)
  have meetings := (T.toEmbeddedCutGraph.distinct_edges_meet_at_endpoints first second distinct
    (T.closedEdgeTarget_in_segment first s) (by rw [targets]; exact T.closedEdgeTarget_in_segment second t)).1
  rcases meetings with left | right
  · have zero : s = 0 := T.closedEdgeTarget_injective first
      ((Subtype.ext left).trans (T.closedEdgeTarget_zero first).symm)
    exact (ne_of_gt positive) zero
  · have one : s = 1 := T.closedEdgeTarget_injective first
      ((Subtype.ext right).trans (T.closedEdgeTarget_one first).symm)
    exact (ne_of_lt before) one

end SixVertexUnfolding.ConvexPolyhedron.CutLocusTree
