import SixVertexUnfolding.Geometry.OctahedralFanShortcuts
import SixVertexUnfolding.Geometry.OctahedralVertexNeighborhood

/-! Positive curvature gives a shorter surface detour between any two
nearby nonpole points. The slit is chosen from the four original fan rays. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set Real OctahedralTriangles

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include small_faces in
/-- One radius works for all pairs of incident triangles and all four slit choices. -/
theorem vertex_detour_radius (pole : Fin 6) :
    ∃ ε > 0, ∀ i j : Fin 4, ∀ x y : Space,
      x ∈ graph.triangle (fanTriangle pole i) → y ∈ graph.triangle (fanTriangle pole j) →
      x ≠ graph.vertex pole → y ≠ graph.vertex pole →
      dist (graph.vertex pole : Space) x ≤ ε → dist (graph.vertex pole : Space) y ≤ ε →
      P.surfaceEDist x y < edist x (graph.vertex pole : Space) + edist (graph.vertex pole : Space) y := by
  classical
  let fan (slit : Fin 4) := Classical.choice (graph.exists_fan_development small_faces pole slit)
  choose radius positive shortcuts using fun slit => (fan slit).exists_point_shortcuts
  let ε := min (min (radius 0) (radius 1)) (min (radius 2) (radius 3))
  have positiveε : 0 < ε := lt_min (lt_min (positive 0) (positive 1)) (lt_min (positive 2) (positive 3))
  have bounded (i : Fin 4) : ε ≤ radius i := by
    fin_cases i
    · exact (min_le_left _ _).trans (min_le_left _ _)
    · exact (min_le_left _ _).trans (min_le_right _ _)
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  have offsets (i : Fin 4) (x : Space) (hx : x ∈ graph.triangle (fanTriangle pole i))
      (nonpole : x ≠ graph.vertex pole) :
      0 ≤ graph.fanOffset pole i x ∧ graph.fanOffset pole i x ≤ graph.fanAngle pole i := by
    have coordinates := (fan i).point_polar_coordinates 0 x (by simpa only [add_zero] using hx) nonpole
    simp only [add_zero] at coordinates
    exact ⟨coordinates.1, coordinates.2.1⟩
  have directed (i j : Fin 4) (x y : Space)
      (hx : x ∈ graph.triangle (fanTriangle pole i)) (hy : y ∈ graph.triangle (fanTriangle pole j))
      (x_ne : x ≠ graph.vertex pole) (y_ne : y ≠ graph.vertex pole)
      (x_small : dist (graph.vertex pole : Space) x ≤ ε) (y_small : dist (graph.vertex pole : Space) y ≤ ε)
      (ordered : graph.fanOffset pole i x ≤ graph.openingAngle pole i (j - i).castSucc + graph.fanOffset pole j y)
      (short : graph.openingAngle pole i (j - i).castSucc + graph.fanOffset pole j y - graph.fanOffset pole i x < π) :
      P.surfaceEDist x y < edist x (graph.vertex pole : Space) + edist (graph.vertex pole : Space) y := by
    have index : i + (j - i) = j := by abel
    have result := shortcuts i 0 (j - i) x y (by simpa only [add_zero] using hx)
      (by simpa only [index] using hy) x_ne y_ne (x_small.trans (bounded i)) (y_small.trans (bounded i))
    simp only [index, add_zero,
      show graph.openingAngle pole i (Fin.castSucc 0) = 0 from rfl, zero_add] at result
    exact result ordered short
  refine ⟨ε, positiveε, ?_⟩
  intro i j x y hx hy x_ne y_ne x_small y_small
  have ox := offsets i x hx x_ne
  have oy := offsets j y hy y_ne
  have reverse_shortcut (ordered : graph.fanOffset pole j y ≤
      graph.openingAngle pole j (i - j).castSucc + graph.fanOffset pole i x)
      (short : graph.openingAngle pole j (i - j).castSucc + graph.fanOffset pole i x - graph.fanOffset pole j y < π) :=
    directed j i y x hy hx y_ne x_ne y_small x_small ordered short
  by_cases same : i = j
  · subst j
    have start : graph.openingAngle pole i (i - i).castSucc = 0 := by simp [openingAngle]
    have angle_small := graph.fanAngle_lt_pi pole i
    rcases le_total (graph.fanOffset pole i x) (graph.fanOffset pole i y) with before | after
    · exact directed i i x y hx hy x_ne y_ne x_small y_small (by rwa [start, zero_add])
        (by rw [start]; linarith [ox.1, oy.2])
    · have result := reverse_shortcut (by rwa [start, zero_add]) (by rw [start]; linarith [oy.1, ox.2])
      simpa only [P.surfaceEDist_comm y x, edist_comm y (graph.vertex pole : Space),
        edist_comm (graph.vertex pole : Space) x, add_comm] using result
  · have complement := graph.complementary_point_angles pole i j same
      (graph.fanOffset pole i x) (graph.fanOffset pole j y) ox oy
    dsimp at complement
    have total := graph.totalAngleAt_lt_two_pi small_faces pole
    by_cases first : graph.openingAngle pole i (j - i).castSucc + graph.fanOffset pole j y - graph.fanOffset pole i x < π
    · exact directed i j x y hx hy x_ne y_ne x_small y_small (by linarith [complement.1]) first
    · have result := reverse_shortcut (by linarith [complement.2.1]) (by linarith [complement.2.2])
      simpa only [P.surfaceEDist_comm y x, edist_comm y (graph.vertex pole : Space),
        edist_comm (graph.vertex pole : Space) x, add_comm] using result

include small_faces in
/-- Any route between nearby nonpole surface points can improve on passing through the vertex. -/
theorem vertex_detour_neighborhood (pole : Fin 6) :
    ∃ U : Set Space, IsOpen U ∧ (graph.vertex pole : Space) ∈ U ∧
      ∀ x ∈ U ∩ frontier P.body, ∀ y ∈ U ∩ frontier P.body,
        x ≠ graph.vertex pole → y ≠ graph.vertex pole →
        P.surfaceEDist x y < edist x (graph.vertex pole : Space) + edist (graph.vertex pole : Space) y := by
  obtain ⟨ε, positive, detours⟩ := graph.vertex_detour_radius small_faces pole
  obtain ⟨V, openV, poleV, fan_cover⟩ := graph.vertex_fan_neighborhood small_faces pole
  refine ⟨V ∩ Metric.ball (graph.vertex pole : Space) ε, openV.inter Metric.isOpen_ball,
    ⟨poleV, Metric.mem_ball_self positive⟩, ?_⟩
  intro x hx y hy x_ne y_ne
  obtain ⟨i, hi⟩ := mem_iUnion.mp (fan_cover ⟨hx.1.1, hx.2⟩)
  obtain ⟨j, hj⟩ := mem_iUnion.mp (fan_cover ⟨hy.1.1, hy.2⟩)
  exact detours i j x y hi hj x_ne y_ne
    (by have bound := hx.1.2; rw [Metric.mem_ball, dist_comm x] at bound; exact bound.le)
    (by have bound := hy.1.2; rw [Metric.mem_ball, dist_comm y] at bound; exact bound.le)

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
