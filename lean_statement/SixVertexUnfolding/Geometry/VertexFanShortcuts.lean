import SixVertexUnfolding.Geometry.VertexFanChords
import SixVertexUnfolding.Geometry.VertexFanAngleComplement

/-! Short angular separation gives a strict intrinsic-distance shortcut. -/

namespace SixVertexUnfolding.ConvexPolyhedron.VertexFaceFan.Development

open Set Real

variable {P : ConvexPolyhedron} {pole : P.Vertex} {n : ℕ} [NeZero n]
  {fan : P.VertexFaceFan pole n}
  {slit : Fin n} (net : fan.Development slit)

include net in
theorem exists_point_shortcuts (deficit : fan.totalAngle < 2 * π) :
    ∃ ε > 0, ∀ i j : Fin n, ∀ x y : Space,
      x ∈ fan.triangle (slit + i) → y ∈ fan.triangle (slit + j) →
      x ≠ pole → y ≠ pole → dist (pole : Space) x ≤ ε → dist (pole : Space) y ≤ ε →
      let α := fan.openingAngle slit i.castSucc + fan.offset (slit + i) x
      let β := fan.openingAngle slit j.castSucc + fan.offset (slit + j) y
      α ≤ β → β - α < π →
      P.surfaceEDist x y < edist x (pole : Space) + edist (pole : Space) y := by
  obtain ⟨fold, ε, positive, inverse, chords⟩ := net.exists_short_chord_paths deficit
  refine ⟨ε, positive, ?_⟩
  intro i j x y hx hy x_ne y_ne x_small y_small α β ordered short
  obtain ⟨x_nonneg, x_bound, x_polar⟩ := net.point_polar_coordinates i x hx x_ne
  obtain ⟨y_nonneg, y_bound, y_polar⟩ := net.point_polar_coordinates j y hy y_ne
  have lower : 0 ≤ α := add_nonneg (fan.openingAngle_nonneg _ _) x_nonneg
  have upper : β ≤ fan.totalAngle := by
    have step := fan.openingAngle_step slit j
    have last := fan.openingAngle_le_total slit j.succ
    dsimp [β]
    linarith
  obtain ⟨path, shorter⟩ := chords (dist (pole : Space) x)
    ⟨dist_pos.mpr x_ne.symm, x_small⟩ (dist (pole : Space) y)
    ⟨dist_pos.mpr y_ne.symm, y_small⟩ α β lower ordered upper short
  have bound := path.surfaceEDist_le_length.trans_lt shorter
  change P.surfaceEDist (fold.map (dist (pole : Space) x • direction α))
    (fold.map (dist (pole : Space) y • direction β)) < _ at bound
  rw [← x_polar, ← y_polar, inverse i x hx, inverse j y hy] at bound
  simpa only [edist_dist, ENNReal.ofReal_add dist_nonneg dist_nonneg, dist_comm x (pole : Space)] using bound

end SixVertexUnfolding.ConvexPolyhedron.VertexFaceFan.Development
