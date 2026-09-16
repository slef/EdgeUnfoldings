import SixVertexUnfolding.Geometry.OctahedralVertexDetours
import SixVertexUnfolding.Geometry.ShortestNonbranching

/-! Shortest routes in the four canonical six-vertex models cannot pass
through another vertex. This discharges vertex avoidance for those models. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)
  {a b : Space}

include graph small_faces in
/-- A simple shortest route never has an original vertex in its interior. -/
theorem simple_shortest_avoids_vertices (path : P.SurfacePath a b)
    (shortest : path.IsShortest) (finite : path.length ≠ ⊤) (simple : Function.Injective path.curve)
    (m : unitInterval) (after_start : 0 < m) (before_end : m < 1) : path.curve m ∉ P.vertices := by
  intro vertex
  obtain ⟨pole, hpole⟩ := graph.vertex.surjective (⟨path.curve m, vertex⟩ : P.Vertex)
  have at_pole : path.curve m = graph.vertex pole := (congrArg Subtype.val hpole).symm
  obtain ⟨U, openU, poleU, detour⟩ := graph.vertex_detour_neighborhood small_faces pole
  obtain ⟨s, t, sm, mt, near⟩ := path.interval_inside_neighborhood m after_start before_end U openU (at_pole ▸ poleU)
  have shorter := detour (path.curve s) ⟨near s ⟨le_rfl, sm.le.trans mt.le⟩, path.on_surface s⟩
    (path.curve t) ⟨near t ⟨sm.le.trans mt.le, le_rfl⟩, path.on_surface t⟩
    (by rw [← at_pole]; exact fun same => sm.ne (simple same))
    (by rw [← at_pole]; exact fun same => mt.ne (simple same).symm)
  rw [← at_pole] at shorter
  have lower : edist (path.curve s) (path.curve m) + edist (path.curve m) (path.curve t) ≤
      P.surfaceEDist (path.curve s) (path.curve t) := by
    rw [← (path.portion s t (sm.le.trans mt.le)).length_eq_surfaceEDist
      (path.portion_shortest shortest finite s t (sm.le.trans mt.le)),
      path.portion_length_split s m t sm.le mt.le]
    exact add_le_add (path.portion s m sm.le).chord_le_length (path.portion m t mt.le).chord_le_length
  exact (not_lt_of_ge lower) shorter

include graph small_faces in
/-- Constant-speed shortest routes between distinct points have vertex-free interiors. -/
theorem shortest_lipschitz_avoids_vertices (path : P.SurfacePath a b) (different : a ≠ b)
    (shortest : path.IsShortest) (finite : path.length ≠ ⊤)
    (speed : LipschitzWith path.length.toNNReal path.curve) :
    ∀ m : unitInterval, 0 < m → m < 1 → path.curve m ∉ P.vertices :=
  graph.simple_shortest_avoids_vertices small_faces path shortest finite
    (path.shortest_lipschitz_injective different shortest finite speed)

include graph small_faces in
/-- The shortest paths required by a star cut can be chosen simple and vertex-avoiding. -/
theorem exists_vertex_avoiding_shortest_path (ha : a ∈ frontier P.body) (hb : b ∈ frontier P.body)
    (different : a ≠ b) :
    ∃ path : P.SurfacePath a b, path.IsShortest ∧ path.length ≠ ⊤ ∧
      LipschitzWith path.length.toNNReal path.curve ∧ Function.Injective path.curve ∧
      ∀ m : unitInterval, 0 < m → m < 1 → path.curve m ∉ P.vertices := by
  obtain ⟨path, shortest, finite, speed, simple⟩ := P.exists_simple_shortest_surface_path ha hb different
  exact ⟨path, shortest, finite, speed, simple,
    graph.simple_shortest_avoids_vertices small_faces path shortest finite simple⟩

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
