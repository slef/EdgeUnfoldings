import SixVertexUnfolding.Geometry.OctahedralJunctionTriangles
import SixVertexUnfolding.Geometry.FourTriangleBoundary

/-! The nine newly separated junction pairs have no closed contact except at their shared vertex. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

/-- Closed nonneighboring triangles in this actual junction share only the uncut equator vertex. -/
theorem junction_meet_only_at_vertex (i : Fin 3) (j k : Fin 4) (intervening : j.val + 1 < k.val)
    (x : Plane) (left : x ∈ net.placedTriangle (junctionIndex i j))
    (right : x ∈ net.placedTriangle (junctionIndex i k)) : x = (net.patch i.castSucc).right := by
  rw [← net.junction_triangle] at left right
  apply (net.junctionChain i).meet_only_at_center _ j k intervening x left right
  rw [net.junction_angle_sum]
  exact graph.totalAngleAt_lt_two_pi small_faces _

theorem neighboring_petals_meet_only_at_vertex (i : Fin 3) (x : Plane)
    (left : x ∈ net.placedTriangle (true, i.castSucc))
    (right : x ∈ net.placedTriangle (true, i.succ)) : x = (net.patch i.castSucc).right :=
  net.junction_meet_only_at_vertex i 0 3 (by decide) x left right

theorem neighboring_petal_fan_meet_only_at_vertex (i : Fin 3) (x : Plane)
    (left : x ∈ net.placedTriangle (true, i.castSucc))
    (right : x ∈ net.placedTriangle (false, i.succ)) : x = (net.patch i.castSucc).right :=
  net.junction_meet_only_at_vertex i 0 2 (by decide) x left right

theorem neighboring_fan_petal_meet_only_at_vertex (i : Fin 3) (x : Plane)
    (left : x ∈ net.placedTriangle (false, i.castSucc))
    (right : x ∈ net.placedTriangle (true, i.succ)) : x = (net.patch i.castSucc).right :=
  net.junction_meet_only_at_vertex i 1 3 (by decide) x left right

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
