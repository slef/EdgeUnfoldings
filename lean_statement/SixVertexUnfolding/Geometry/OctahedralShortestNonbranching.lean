import SixVertexUnfolding.Geometry.OctahedralVertexAvoidance

/-! For canonical six-vertex polyhedra, common endpoints and an interior
meeting force two shortest routes to coincide, without an avoidance premise. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)
  {a b : Space}

include graph small_faces in
/-- An interior meeting determines the whole shortest route. -/
theorem shortest_routes_agree_of_meeting (first second : P.SurfacePath a b) (different : a ≠ b)
    (first_shortest : first.IsShortest) (second_shortest : second.IsShortest)
    (first_finite : first.length ≠ ⊤) (second_finite : second.length ≠ ⊤)
    (first_speed : LipschitzWith first.length.toNNReal first.curve)
    (second_speed : LipschitzWith second.length.toNNReal second.curve)
    (m : unitInterval) (after_start : 0 < m) (before_end : m < 1)
    (meet : first.curve m = second.curve m) : ∀ t, first.curve t = second.curve t :=
  first.agree_of_interior_meeting second first_shortest second_shortest first_finite second_finite
    first_speed second_speed
    (graph.shortest_lipschitz_avoids_vertices small_faces first different first_shortest first_finite first_speed)
    m after_start before_end meet

include graph small_faces in
/-- Distinct shortest routes with the same endpoints have disjoint open traces. -/
theorem distinct_shortest_routes_disjoint (first second : P.SurfacePath a b) (different : a ≠ b)
    (first_shortest : first.IsShortest) (second_shortest : second.IsShortest)
    (first_finite : first.length ≠ ⊤) (second_finite : second.length ≠ ⊤)
    (first_speed : LipschitzWith first.length.toNNReal first.curve)
    (second_speed : LipschitzWith second.length.toNNReal second.curve)
    (distinct_routes : ¬ ∀ t, first.curve t = second.curve t) :
    Disjoint (first.curve '' Ioo (0 : unitInterval) 1) (second.curve '' Ioo (0 : unitInterval) 1) :=
  first.disjoint_open_traces second different first_shortest second_shortest first_finite second_finite
    first_speed second_speed
    (graph.shortest_lipschitz_avoids_vertices small_faces first different first_shortest first_finite first_speed)
    distinct_routes

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
