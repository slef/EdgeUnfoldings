import SixVertexUnfolding.Geometry.FiveFaceFanAvoidance

/-! Vertex avoidance for a six-vertex convex polyhedron at a vertex joined
by edges to all five others. The fan, curvature, and detours are constructed
from the actual polyhedron; they are not additional hypotheses. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

variable {P : ConvexPolyhedron} (size : P.vertices.card = 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)
  (pole : P.Vertex) (universal : ∀ v : P.Vertex, v ≠ pole → P.edgeGraph.Adj pole v)
  {a b : Space}

include size small_faces universal in
/-- Nearby surface points admit a strict shortcut around a universal vertex. -/
theorem universal_vertex_detour_neighborhood :
    ∃ U : Set Space, IsOpen U ∧ (pole : Space) ∈ U ∧
      ∀ x ∈ U ∩ frontier P.body, ∀ y ∈ U ∩ frontier P.body,
        x ≠ pole → y ≠ pole →
        P.surfaceEDist x y < edist x (pole : Space) + edist (pole : Space) y := by
  obtain ⟨fan⟩ := P.exists_universal_five_face_fan size small_faces pole universal
  exact fan.vertex_detour_neighborhood

include size small_faces universal in
/-- A simple shortest path cannot pass through a universal vertex. -/
theorem simple_shortest_avoids_universal_vertex (path : P.SurfacePath a b)
    (shortest : path.IsShortest) (finite : path.length ≠ ⊤)
    (simple : Function.Injective path.curve) :
    ∀ m : unitInterval, 0 < m → m < 1 → path.curve m ≠ pole := by
  obtain ⟨fan⟩ := P.exists_universal_five_face_fan size small_faces pole universal
  exact fan.simple_shortest_avoids_pole path shortest finite simple

include size small_faces universal in
/-- Constant-speed shortest paths between distinct endpoints avoid the universal vertex. -/
theorem shortest_lipschitz_avoids_universal_vertex (path : P.SurfacePath a b)
    (different : a ≠ b) (shortest : path.IsShortest) (finite : path.length ≠ ⊤)
    (speed : LipschitzWith path.length.toNNReal path.curve) :
    ∀ m : unitInterval, 0 < m → m < 1 → path.curve m ≠ pole := by
  obtain ⟨fan⟩ := P.exists_universal_five_face_fan size small_faces pole universal
  exact fan.shortest_lipschitz_avoids_pole path different shortest finite speed

include size small_faces universal in
/-- The finite simple shortest routes can be chosen with this vertex excluded internally. -/
theorem exists_universal_vertex_avoiding_shortest_path
    (ha : a ∈ frontier P.body) (hb : b ∈ frontier P.body) (different : a ≠ b) :
    ∃ path : P.SurfacePath a b, path.IsShortest ∧ path.length ≠ ⊤ ∧
      LipschitzWith path.length.toNNReal path.curve ∧ Function.Injective path.curve ∧
      ∀ m : unitInterval, 0 < m → m < 1 → path.curve m ≠ pole := by
  obtain ⟨path, shortest, finite, speed, simple⟩ :=
    P.exists_simple_shortest_surface_path ha hb different
  exact ⟨path, shortest, finite, speed, simple,
    simple_shortest_avoids_universal_vertex size small_faces pole universal
      path shortest finite simple⟩

end SixVertexUnfolding.ConvexPolyhedron
