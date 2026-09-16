import SixVertexUnfolding.Geometry.EmbeddedGraphComponents

/-! Distinct closed edges of the embedded cut graph can meet only
at vertices that are endpoints of both edges. -/

namespace SixVertexUnfolding.ConvexPolyhedron.EmbeddedCutGraph

open Set

variable {P : ConvexPolyhedron} {a : frontier P.body} (K : P.EmbeddedCutGraph a)

theorem distinct_edges_meet_at_endpoints {u v w z : K.vertices}
    (first : K.graph.Adj u v) (second : K.graph.Adj w z)
    (different : ¬ ((u = w ∧ v = z) ∨ (u = z ∧ v = w))) {x : Space}
    (left : x ∈ segment ℝ (u : Space) (v : Space))
    (right : x ∈ segment ℝ (w : Space) (z : Space)) :
    (x = (u : Space) ∨ x = (v : Space)) ∧ (x = (w : Space) ∨ x = (z : Space)) := by
  have vertex : x ∈ K.vertices := by
    by_contra outside
    have interior {p q : K.vertices} (member : x ∈ segment ℝ (p : Space) (q : Space)) :
        x ∈ openSegment ℝ (p : Space) (q : Space) :=
      mem_openSegment_of_ne_left_right (fun same => outside (same ▸ p.property))
        (fun same => outside (same ▸ q.property)) member
    exact different (K.open_edges_meet u v w z first second x (interior left) (interior right))
  let point : K.vertices := ⟨x, vertex⟩
  have first_endpoint := K.vertex_on_edge first
    (show (point : Space) ∈ segment ℝ (u : Space) (v : Space) from left)
  have second_endpoint := K.vertex_on_edge second
    (show (point : Space) ∈ segment ℝ (w : Space) (z : Space) from right)
  constructor
  · exact first_endpoint.imp (congrArg Subtype.val) (congrArg Subtype.val)
  · exact second_endpoint.imp (congrArg Subtype.val) (congrArg Subtype.val)

end SixVertexUnfolding.ConvexPolyhedron.EmbeddedCutGraph
