import SixVertexUnfolding.Geometry.JunctionAngleSum
import SixVertexUnfolding.Geometry.SmallPolyhedronJunctionOrder

/-! The actual metric triangles around a flat cut-tree junction have
total corner angle exactly 2π. Each incident edge is counted once.
The assertion is independent of the chosen metric models.

Here the shortest-route inputs come from the actual vertex fans of a
polyhedron with at most six vertices and triangular/quadrilateral faces.
No canonical graph model is assumed. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Real Set EuclideanGeometry
open scoped BigOperators

variable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include size small_faces in
/-- No chart or angular ordering needs to be supplied: the actual
nonvertex cut junction itself supplies the full-turn angle identity. -/
theorem small_sum_nonvertex_junction_angles (a : frontier P.body) (T : P.CutLocusTree a)
    (u : T.vertices) (not_vertex : (u : Space) ∉ P.vertices)
    [Fintype {v : T.vertices // T.graph.Adj u v}]
    (models : ∀ v : {v : T.vertices // T.graph.Adj u v}, CutEdgeMetricModel T v.property) :
    ∑ v, (angle (models v).first (models v).left (models v).right +
      angle (models v).second (models v).left (models v).right) = 2 * π := by
  obtain ⟨order⟩ := small_exists_junction_order size small_faces a T u not_vertex
  exact order.sum_junction_angles models

end SixVertexUnfolding.ConvexPolyhedron
