import SixVertexUnfolding.Geometry.VertexFanAvoidance

/-! Shortest paths avoid every original vertex internally, for any convex
polyhedron with at most six vertices and triangular or quadrilateral faces.
This includes the universal-vertex family without a canonical graph premise. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

variable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)
  {a b : Space}

include size small_faces in
/-- Every original vertex admits a strict local surface detour. -/
theorem small_vertex_detour_neighborhood (pole : P.Vertex) :
    ∃ U : Set Space, IsOpen U ∧ (pole : Space) ∈ U ∧
      ∀ x ∈ U ∩ frontier P.body, ∀ y ∈ U ∩ frontier P.body,
        x ≠ pole → y ≠ pole →
        P.surfaceEDist x y < edist x (pole : Space) + edist (pole : Space) y := by
  letI : NeZero (P.edgeGraph.degree pole) := ⟨by have := P.edgeGraph_min_degree pole; omega⟩
  obtain ⟨fan⟩ := P.exists_vertex_face_fan size small_faces pole
    (n := P.edgeGraph.degree pole) rfl
  exact fan.vertex_detour_neighborhood size small_faces

include size small_faces in
/-- A simple finite shortest path cannot pass through any original vertex. -/
theorem small_simple_shortest_avoids_vertices (path : P.SurfacePath a b)
    (shortest : path.IsShortest) (finite : path.length ≠ ⊤)
    (simple : Function.Injective path.curve) :
    ∀ m : unitInterval, 0 < m → m < 1 → path.curve m ∉ P.vertices := by
  intro m after_start before_end at_vertex
  let pole : P.Vertex := ⟨path.curve m, at_vertex⟩
  letI : NeZero (P.edgeGraph.degree pole) := ⟨by have := P.edgeGraph_min_degree pole; omega⟩
  obtain ⟨fan⟩ := P.exists_vertex_face_fan size small_faces pole
    (n := P.edgeGraph.degree pole) rfl
  exact fan.simple_shortest_avoids_pole size small_faces path shortest finite simple
    m after_start before_end rfl

include size small_faces in
/-- Constant-speed shortest paths between distinct endpoints have vertex-free interiors. -/
theorem small_shortest_lipschitz_avoids_vertices (path : P.SurfacePath a b)
    (different : a ≠ b) (shortest : path.IsShortest) (finite : path.length ≠ ⊤)
    (speed : LipschitzWith path.length.toNNReal path.curve) :
    ∀ m : unitInterval, 0 < m → m < 1 → path.curve m ∉ P.vertices :=
  small_simple_shortest_avoids_vertices size small_faces path shortest finite
    (path.shortest_lipschitz_injective different shortest finite speed)

include size small_faces in
/-- The shortest routes needed for the star construction can be chosen vertex-avoiding. -/
theorem small_exists_vertex_avoiding_shortest_path
    (ha : a ∈ frontier P.body) (hb : b ∈ frontier P.body) (different : a ≠ b) :
    ∃ path : P.SurfacePath a b, path.IsShortest ∧ path.length ≠ ⊤ ∧
      LipschitzWith path.length.toNNReal path.curve ∧ Function.Injective path.curve ∧
      ∀ m : unitInterval, 0 < m → m < 1 → path.curve m ∉ P.vertices := by
  obtain ⟨path, shortest, finite, speed, simple⟩ :=
    P.exists_simple_shortest_surface_path ha hb different
  exact ⟨path, shortest, finite, speed, simple,
    small_simple_shortest_avoids_vertices size small_faces path shortest finite simple⟩

end SixVertexUnfolding.ConvexPolyhedron
