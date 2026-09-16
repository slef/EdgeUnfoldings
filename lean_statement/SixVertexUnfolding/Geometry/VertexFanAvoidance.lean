import SixVertexUnfolding.Geometry.VertexFanDetours
import SixVertexUnfolding.Geometry.ShortestNonbranching

/-! A shortest path cannot pass through the vertex of the actual corner fan:
the local surface detour would strictly shorten that path. -/

namespace SixVertexUnfolding.ConvexPolyhedron.VertexFaceFan

open Set

variable {P : ConvexPolyhedron} {pole : P.Vertex} {n : ℕ} [NeZero n]
  (fan : P.VertexFaceFan pole n) (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)
  {a b : Space}

include fan size small_faces in
/-- A simple shortest route avoids this vertex at every interior time. -/
theorem simple_shortest_avoids_pole (path : P.SurfacePath a b)
    (shortest : path.IsShortest) (finite : path.length ≠ ⊤)
    (simple : Function.Injective path.curve)
    (m : unitInterval) (after_start : 0 < m) (before_end : m < 1) :
    path.curve m ≠ pole := by
  intro at_pole
  obtain ⟨U, openU, poleU, detour⟩ := fan.vertex_detour_neighborhood size small_faces
  obtain ⟨s, t, sm, mt, near⟩ := path.interval_inside_neighborhood m
    after_start before_end U openU (at_pole ▸ poleU)
  have shorter := detour (path.curve s)
    ⟨near s ⟨le_rfl, sm.le.trans mt.le⟩, path.on_surface s⟩
    (path.curve t) ⟨near t ⟨sm.le.trans mt.le, le_rfl⟩, path.on_surface t⟩
    (by rw [← at_pole]; exact fun same => sm.ne (simple same))
    (by rw [← at_pole]; exact fun same => mt.ne (simple same).symm)
  rw [← at_pole] at shorter
  have lower : edist (path.curve s) (path.curve m) + edist (path.curve m) (path.curve t) ≤
      P.surfaceEDist (path.curve s) (path.curve t) := by
    rw [← (path.portion s t (sm.le.trans mt.le)).length_eq_surfaceEDist
      (path.portion_shortest shortest finite s t (sm.le.trans mt.le)),
      path.portion_length_split s m t sm.le mt.le]
    exact add_le_add (path.portion s m sm.le).chord_le_length
      (path.portion m t mt.le).chord_le_length
  exact (not_lt_of_ge lower) shorter

include fan size small_faces in
/-- Constant-speed shortest routes between distinct endpoints avoid the vertex. -/
theorem shortest_lipschitz_avoids_pole (path : P.SurfacePath a b) (different : a ≠ b)
    (shortest : path.IsShortest) (finite : path.length ≠ ⊤)
    (speed : LipschitzWith path.length.toNNReal path.curve) :
    ∀ m : unitInterval, 0 < m → m < 1 → path.curve m ≠ pole :=
  fan.simple_shortest_avoids_pole size small_faces path shortest finite
    (path.shortest_lipschitz_injective different shortest finite speed)

end SixVertexUnfolding.ConvexPolyhedron.VertexFaceFan
