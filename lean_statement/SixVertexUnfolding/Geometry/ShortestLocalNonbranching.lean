import SixVertexUnfolding.Geometry.ShortestFlatCoordinates
import SixVertexUnfolding.Geometry.ShortestCrossDistances

/-! Two minimizing routes with the same endpoints cannot cross and separate
at a nonvertex point. The proof uses their actual intrinsic distances and flat charts. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SurfacePath

open Set

variable {P : ConvexPolyhedron} {a b z : Space}

/-- In one flat chart, two shortest routes meeting between the endpoints agree on the whole interval. -/
theorem agree_on_flat_interval (first second : P.SurfacePath a b)
    (first_shortest : first.IsShortest) (second_shortest : second.IsShortest)
    (first_finite : first.length ≠ ⊤) (second_finite : second.length ≠ ⊤)
    (first_speed : LipschitzWith first.length.toNNReal first.curve)
    (second_speed : LipschitzWith second.length.toNNReal second.curve)
    (chart : P.FlatChart z) (s m t : unitInterval) (sm : s < m) (mt : m < t)
    (meet : first.curve m = second.curve m)
    (first_in : ∀ u ∈ Icc s t, first.curve u ∈ chart.map '' chart.domain)
    (second_in : ∀ u ∈ Icc s t, second.curve u ∈ chart.map '' chart.domain) :
    ∀ u ∈ Icc s t, first.curve u = second.curve u := by
  let r := ((m : ℝ) - (s : ℝ)) / ((t : ℝ) - (s : ℝ))
  have denominator : 0 < (t : ℝ) - (s : ℝ) := sub_pos.mpr (sm.trans mt)
  have positive : 0 < r := div_pos (sub_pos.mpr sm) denominator
  have before_one : r < 1 := (div_lt_one denominator).mpr (by change (m : ℝ) - (s : ℝ) < (t : ℝ) - (s : ℝ); linarith [show (m : ℝ) < (t : ℝ) from mt])
  have first_start := first_in s ⟨le_rfl, (sm.trans mt).le⟩
  have first_middle := first_in m ⟨sm.le, mt.le⟩
  have first_end := first_in t ⟨(sm.trans mt).le, le_rfl⟩
  have second_start := second_in s ⟨le_rfl, (sm.trans mt).le⟩
  have second_middle := second_in m ⟨sm.le, mt.le⟩
  have second_end := second_in t ⟨(sm.trans mt).le, le_rfl⟩
  have first_affine := first.coordinates_eq_lineMap first_shortest first_finite first_speed chart s t (sm.trans mt) first_in
  have second_affine := second.coordinates_eq_lineMap second_shortest second_finite second_speed chart s t (sm.trans mt) second_in
  have middle_first := first_affine m ⟨sm.le, mt.le⟩
  have middle_second := second_affine m ⟨sm.le, mt.le⟩
  rw [← meet] at middle_second
  have elapsed (v w : unitInterval) (vw : v ≤ w) : dist v w = (w : ℝ) - (v : ℝ) := by
    change dist (v : ℝ) (w : ℝ) = _
    rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (show (v : ℝ) ≤ (w : ℝ) from vw))]
  have middle_cross : chart.coordinates (first.curve m) =
      AffineMap.lineMap (chart.coordinates (first.curve s)) (chart.coordinates (second.curve t)) r := by
    apply point_eq_lineMap_of_distance_ratios _ _ _ (s : ℝ) (m : ℝ) (t : ℝ) first.length.toReal (sm.trans mt) sm.le mt.le
    · rw [first.coordinate_distance first_shortest first_finite first_speed chart s m first_start first_middle, elapsed s m sm.le]
    · rw [meet, second.coordinate_distance second_shortest second_finite second_speed chart m t second_middle second_end,
        ← first.shortest_lengths_equal second first_shortest second_shortest, elapsed m t mt.le]
    · rw [chart.coordinates_distance first_start second_end,
        first.cross_distance_eq_of_meet second first_shortest second_shortest first_finite second_finite
          first_speed second_speed s m t sm.le mt.le meet]
  have end_equal : chart.coordinates (first.curve t) = chart.coordinates (second.curve t) :=
    lineMap_right_unique _ _ _ r positive.ne' (middle_first.symm.trans middle_cross)
  have start_equal : chart.coordinates (first.curve s) = chart.coordinates (second.curve s) :=
    lineMap_left_unique _ _ _ r before_one.ne (middle_cross.symm.trans middle_second)
  intro u hu
  calc
    first.curve u = chart.map (chart.coordinates (first.curve u)) := (chart.map_coordinates (first_in u hu)).symm
    _ = chart.map (chart.coordinates (second.curve u)) := by
      rw [first_affine u hu, second_affine u hu, start_equal, end_equal]
    _ = second.curve u := chart.map_coordinates (second_in u hu)

/-- A common nonvertex interior point forces local agreement of both shortest routes. -/
theorem agree_near_nonvertex_meeting (first second : P.SurfacePath a b)
    (first_shortest : first.IsShortest) (second_shortest : second.IsShortest)
    (first_finite : first.length ≠ ⊤) (second_finite : second.length ≠ ⊤)
    (first_speed : LipschitzWith first.length.toNNReal first.curve)
    (second_speed : LipschitzWith second.length.toNNReal second.curve)
    (m : unitInterval) (after_start : 0 < m) (before_end : m < 1)
    (meet : first.curve m = second.curve m) (not_vertex : first.curve m ∉ P.vertices) :
    ∃ s t : unitInterval, s < m ∧ m < t ∧ ∀ u ∈ Icc s t, first.curve u = second.curve u := by
  obtain ⟨chart⟩ := P.exists_flat_chart (first.on_surface m) not_vertex
  obtain ⟨U, openU, center, covers⟩ := chart.covers
  obtain ⟨s₁, t₁, sm₁, mt₁, first_near⟩ := first.interval_inside_neighborhood m after_start before_end U openU center
  obtain ⟨s₂, t₂, sm₂, mt₂, second_near⟩ := second.interval_inside_neighborhood m after_start before_end U openU (meet ▸ center)
  let s := max s₁ s₂
  let t := min t₁ t₂
  have sm : s < m := max_lt sm₁ sm₂
  have mt : m < t := lt_min mt₁ mt₂
  have first_in : ∀ u ∈ Icc s t, first.curve u ∈ chart.map '' chart.domain := by
    intro u hu
    exact covers ⟨first_near u ⟨(le_max_left _ _).trans hu.1, hu.2.trans (min_le_left _ _)⟩, first.on_surface u⟩
  have second_in : ∀ u ∈ Icc s t, second.curve u ∈ chart.map '' chart.domain := by
    intro u hu
    exact covers ⟨second_near u ⟨(le_max_right _ _).trans hu.1, hu.2.trans (min_le_right _ _)⟩, second.on_surface u⟩
  exact ⟨s, t, sm, mt, first.agree_on_flat_interval second first_shortest second_shortest
    first_finite second_finite first_speed second_speed chart s m t sm mt meet first_in second_in⟩

end SixVertexUnfolding.ConvexPolyhedron.SurfacePath
