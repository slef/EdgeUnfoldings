import SixVertexUnfolding.Geometry.FiveFaceFanShortcuts
import SixVertexUnfolding.Geometry.NonvertexFacetNeighborhoods

/-! Positive curvature gives a shorter surface detour between any two
nearby nonpole points. The slit is chosen from the five original fan rays. -/

namespace SixVertexUnfolding.ConvexPolyhedron.FiveFaceFan

open Set Real

variable {P : ConvexPolyhedron} {pole : P.Vertex} (fan : P.FiveFaceFan pole)

/-- One radius works for all pairs of incident triangles and all five slit choices. -/
theorem vertex_detour_radius :
    ∃ ε > 0, ∀ i j : Fin 5, ∀ x y : Space,
      x ∈ fan.triangle i → y ∈ fan.triangle j →
      x ≠ pole → y ≠ pole →
      dist (pole : Space) x ≤ ε → dist (pole : Space) y ≤ ε →
      P.surfaceEDist x y < edist x (pole : Space) + edist (pole : Space) y := by
  classical
  let net (slit : Fin 5) := Classical.choice (fan.exists_development slit)
  choose radius positive shortcuts using fun slit => (net slit).exists_point_shortcuts
  let ε := min (min (radius 0) (radius 1)) (min (radius 2) (min (radius 3) (radius 4)))
  have positiveε : 0 < ε := lt_min (lt_min (positive 0) (positive 1)) (lt_min (positive 2) (lt_min (positive 3) (positive 4)))
  have bounded (i : Fin 5) : ε ≤ radius i := by
    fin_cases i
    · exact (min_le_left _ _).trans (min_le_left _ _)
    · exact (min_le_left _ _).trans (min_le_right _ _)
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have offsets (i : Fin 5) (x : Space) (hx : x ∈ fan.triangle i)
      (nonpole : x ≠ pole) :
      0 ≤ fan.offset i x ∧ fan.offset i x ≤ fan.sectorAngle i := by
    have coordinates := (net i).point_polar_coordinates 0 x (by simpa only [add_zero] using hx) nonpole
    simp only [add_zero] at coordinates
    exact ⟨coordinates.1, coordinates.2.1⟩
  have directed (i j : Fin 5) (x y : Space)
      (hx : x ∈ fan.triangle i) (hy : y ∈ fan.triangle j)
      (x_ne : x ≠ pole) (y_ne : y ≠ pole)
      (x_small : dist (pole : Space) x ≤ ε) (y_small : dist (pole : Space) y ≤ ε)
      (ordered : fan.offset i x ≤ fan.openingAngle i (j - i).castSucc + fan.offset j y)
      (short : fan.openingAngle i (j - i).castSucc + fan.offset j y - fan.offset i x < π) :
      P.surfaceEDist x y < edist x (pole : Space) + edist (pole : Space) y := by
    have index : i + (j - i) = j := by abel
    have result := shortcuts i 0 (j - i) x y (by simpa only [add_zero] using hx)
      (by simpa only [index] using hy) x_ne y_ne (x_small.trans (bounded i)) (y_small.trans (bounded i))
    simp only [index, add_zero,
      show fan.openingAngle i (Fin.castSucc 0) = 0 from rfl, zero_add] at result
    exact result ordered short
  refine ⟨ε, positiveε, ?_⟩
  intro i j x y hx hy x_ne y_ne x_small y_small
  have ox := offsets i x hx x_ne
  have oy := offsets j y hy y_ne
  have reverse_shortcut (ordered : fan.offset j y ≤
      fan.openingAngle j (i - j).castSucc + fan.offset i x)
      (short : fan.openingAngle j (i - j).castSucc + fan.offset i x - fan.offset j y < π) :=
    directed j i y x hy hx y_ne x_ne y_small x_small ordered short
  by_cases same : i = j
  · subst j
    have start : fan.openingAngle i (i - i).castSucc = 0 := by simp [openingAngle]
    have angle_small := fan.sectorAngle_lt_pi i
    rcases le_total (fan.offset i x) (fan.offset i y) with before | after
    · exact directed i i x y hx hy x_ne y_ne x_small y_small (by rwa [start, zero_add])
        (by rw [start]; linarith [ox.1, oy.2])
    · have result := reverse_shortcut (by rwa [start, zero_add]) (by rw [start]; linarith [oy.1, ox.2])
      simpa only [P.surfaceEDist_comm y x, edist_comm y (pole : Space),
        edist_comm (pole : Space) x, add_comm] using result
  · have complement := fan.complementary_point_angles i j same
      (fan.offset i x) (fan.offset j y) ox oy
    dsimp at complement
    have total := fan.totalAngle_lt_two_pi
    by_cases first : fan.openingAngle i (j - i).castSucc + fan.offset j y - fan.offset i x < π
    · exact directed i j x y hx hy x_ne y_ne x_small y_small (by linarith [complement.1]) first
    · have result := reverse_shortcut (by linarith [complement.2.1]) (by linarith [complement.2.2])
      simpa only [P.surfaceEDist_comm y x, edist_comm y (pole : Space),
        edist_comm (pole : Space) x, add_comm] using result

/-- These same five triangles cover a whole neighborhood on the actual surface. -/
theorem surface_neighborhood :
    ∃ U : Set Space, IsOpen U ∧ (pole : Space) ∈ U ∧
      U ∩ frontier P.body ⊆ ⋃ i : Fin 5, fan.triangle i := by
  obtain ⟨U, openU, poleU, incident⟩ := P.incident_facets_neighborhood pole
  refine ⟨U, openU, poleU, ?_⟩
  rintro x ⟨near, surface⟩
  obtain ⟨F, member⟩ := P.boundary_point_in_face surface
  obtain ⟨i, rfl⟩ := (fan.covers F).mp (incident x near F member)
  exact mem_iUnion.mpr ⟨i, by rwa [fan.triangle_eq_face]⟩

include fan in
/-- Any route between nearby nonpole surface points can improve on passing through the vertex. -/
theorem vertex_detour_neighborhood :
    ∃ U : Set Space, IsOpen U ∧ (pole : Space) ∈ U ∧
      ∀ x ∈ U ∩ frontier P.body, ∀ y ∈ U ∩ frontier P.body,
        x ≠ pole → y ≠ pole →
        P.surfaceEDist x y < edist x (pole : Space) + edist (pole : Space) y := by
  obtain ⟨ε, positive, detours⟩ := fan.vertex_detour_radius
  obtain ⟨V, openV, poleV, fan_cover⟩ := fan.surface_neighborhood
  refine ⟨V ∩ Metric.ball (pole : Space) ε, openV.inter Metric.isOpen_ball,
    ⟨poleV, Metric.mem_ball_self positive⟩, ?_⟩
  intro x hx y hy x_ne y_ne
  obtain ⟨i, hi⟩ := mem_iUnion.mp (fan_cover ⟨hx.1.1, hx.2⟩)
  obtain ⟨j, hj⟩ := mem_iUnion.mp (fan_cover ⟨hy.1.1, hy.2⟩)
  exact detours i j x y hi hj x_ne y_ne
    (by have bound := hx.1.2; rw [Metric.mem_ball, dist_comm x] at bound; exact bound.le)
    (by have bound := hy.1.2; rw [Metric.mem_ball, dist_comm y] at bound; exact bound.le)

end SixVertexUnfolding.ConvexPolyhedron.FiveFaceFan
