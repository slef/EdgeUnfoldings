import SixVertexUnfolding.Geometry.OctahedralFanChords
import SixVertexUnfolding.Geometry.OctahedralFanAngleComplement

/-! Chord detours between actual surface points, expressed using intrinsic
distance and their ordinary angular coordinates. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.FanDevelopment

open Set OctahedralTriangles Real

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
  {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4}
  {pole : Fin 6} {slit : Fin 4} (fan : graph.FanDevelopment small_faces pole slit)

include fan in
/-- Near the pole, a short angular separation strictly improves on the path through the pole. -/
theorem exists_point_shortcuts :
    ∃ ε > 0, ∀ i j : Fin 4, ∀ x y : Space,
      x ∈ graph.triangle (fanTriangle pole (slit + i)) →
      y ∈ graph.triangle (fanTriangle pole (slit + j)) →
      x ≠ graph.vertex pole → y ≠ graph.vertex pole →
      dist (graph.vertex pole : Space) x ≤ ε → dist (graph.vertex pole : Space) y ≤ ε →
      let α := graph.openingAngle pole slit i.castSucc + graph.fanOffset pole (slit + i) x
      let β := graph.openingAngle pole slit j.castSucc + graph.fanOffset pole (slit + j) y
      α ≤ β → β - α < π →
      P.surfaceEDist x y < edist x (graph.vertex pole : Space) + edist (graph.vertex pole : Space) y := by
  obtain ⟨fold, ε, positive, inverse, chords⟩ := fan.exists_short_chord_paths
  refine ⟨ε, positive, ?_⟩
  intro i j x y hx hy x_ne y_ne x_small y_small α β ordered short
  obtain ⟨x_nonneg, x_bound, x_polar⟩ := fan.point_polar_coordinates i x hx x_ne
  obtain ⟨y_nonneg, y_bound, y_polar⟩ := fan.point_polar_coordinates j y hy y_ne
  have lower : 0 ≤ α := add_nonneg (graph.openingAngle_nonneg _ _ _) x_nonneg
  have upper : β ≤ graph.totalAngleAt pole := by
    have step := graph.openingAngle_step pole slit j
    have last := graph.openingAngle_le_total pole slit j.succ
    dsimp [β]
    linarith
  obtain ⟨path, shorter⟩ := chords (dist (graph.vertex pole : Space) x)
    ⟨dist_pos.mpr x_ne.symm, x_small⟩ (dist (graph.vertex pole : Space) y)
    ⟨dist_pos.mpr y_ne.symm, y_small⟩ α β lower ordered upper short
  have bound := path.surfaceEDist_le_length.trans_lt shorter
  change P.surfaceEDist (fold.map (dist (graph.vertex pole : Space) x • direction α))
    (fold.map (dist (graph.vertex pole : Space) y • direction β)) < _ at bound
  rw [← x_polar, ← y_polar, inverse i x hx, inverse j y hy] at bound
  simpa only [edist_dist, ENNReal.ofReal_add dist_nonneg dist_nonneg,
    dist_comm x (graph.vertex pole : Space)] using bound

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.FanDevelopment
