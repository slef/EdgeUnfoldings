import SixVertexUnfolding.Geometry.CircularSourceOrder
import SixVertexUnfolding.Geometry.VoronoiDiagram

/-! A gap between consecutive circular source copies determines an actual
Voronoi ray. Its two endpoint sources tie, and every other source is strictly
farther away. Gaps larger than a half turn are allowed.
-/

namespace SixVertexUnfolding

open Real Set

private theorem cos_le_away {δ φ : ℝ} (nonnegative : 0 ≤ δ)
    (lower : δ ≤ φ) (upper : φ ≤ 2 * π - δ) : cos φ ≤ cos δ := by
  by_cases first : φ ≤ π
  · exact cos_le_cos_of_nonneg_of_le_pi nonnegative first lower
  · have reflected : cos (2 * π - φ) = cos φ := by simp [cos_sub]
    rw [← reflected]
    exact cos_le_cos_of_nonneg_of_le_pi nonnegative (by linarith) (by linarith)

private theorem cos_lt_away {δ φ : ℝ} (nonnegative : 0 ≤ δ)
    (lower : δ < φ) (upper : φ < 2 * π - δ) : cos φ < cos δ := by
  by_cases first : φ ≤ π
  · exact cos_lt_cos_of_nonneg_of_le_pi nonnegative first lower
  · have reflected : cos (2 * π - φ) = cos φ := by simp [cos_sub]
    rw [← reflected]
    exact cos_lt_cos_of_nonneg_of_le_pi nonnegative (by linarith) (by linarith)

/-- The nearest-site comparison is unchanged by translating both circles. -/
private theorem circle_distance_sq (z : Plane) (R ρ α φ : ℝ) :
    dist (z + R • direction α) (z + ρ • direction φ) ^ 2 =
      R ^ 2 + ρ ^ 2 - 2 * R * ρ * cos (φ - α) := by
  rw [dist_add_left]
  exact polar_distance_sq R ρ α φ

/-- If the open angular gap from `α` to `β` contains no source, its bisecting
ray is a cut ray with exactly those two nearest source copies. -/
theorem circular_gap_voronoi_ray (sources : Set Plane) (z : Plane) {R α β ρ : ℝ}
    (radius_positive : 0 < R) (sample_positive : 0 < ρ)
    (ordered : α < β) (one_turn : β < α + 2 * π)
    (first : z + R • direction α ∈ sources) (second : z + R • direction β ∈ sources)
    (empty_gap : ∀ p ∈ sources, ∃ φ ∈ Icc β (α + 2 * π), p = z + R • direction φ) :
    let p := z + R • direction α
    let q := z + R • direction β
    let x := z + ρ • direction ((α + β) / 2)
    p ≠ q ∧ x ∈ voronoiBoundary sources ∧ x ∈ voronoiRidge sources p q ∧
      ∀ s ∈ sources, s ≠ p → s ≠ q → dist p x < dist s x := by
  let m := (α + β) / 2
  let δ := (β - α) / 2
  have delta_positive : 0 < δ := by dsimp [δ]; linarith
  have cosine_p : cos (m - α) = cos δ := by congr 1; dsimp [m, δ]; ring
  have cosine_q : cos (m - β) = cos δ := by
    rw [show m - β = -δ by dsimp [m, δ]; ring, cos_neg]
  have distinct : z + R • direction α ≠ z + R • direction β := by
    intro same
    have angles := polar_angle_eq_of_one_turn R R α β radius_positive radius_positive
      (by linarith [pi_pos]) (by linarith) (add_left_cancel same)
    linarith
  have tied : dist (z + R • direction α) (z + ρ • direction m) =
      dist (z + R • direction β) (z + ρ • direction m) := by
    have left := circle_distance_sq z R ρ α m
    have right := circle_distance_sq z R ρ β m
    rw [cosine_p] at left
    rw [cosine_q] at right
    nlinarith [(dist_nonneg : 0 ≤ dist (z + R • direction α) (z + ρ • direction m)),
      (dist_nonneg : 0 ≤ dist (z + R • direction β) (z + ρ • direction m))]
  have nearest (s : Plane) (hs : s ∈ sources) :
      dist (z + R • direction α) (z + ρ • direction m) ≤ dist s (z + ρ • direction m) := by
    obtain ⟨φ, interval, rfl⟩ := empty_gap s hs
    have cosine : cos (m - φ) ≤ cos δ := by
      rw [show m - φ = -(φ - m) by ring, cos_neg]
      exact cos_le_away delta_positive.le (by dsimp [δ, m]; linarith [interval.1])
        (by dsimp [δ, m]; linarith [interval.2])
    have scaled := mul_le_mul_of_nonneg_left cosine (show 0 ≤ 2 * R * ρ by positivity)
    have left := circle_distance_sq z R ρ α m
    rw [cosine_p] at left
    have right := circle_distance_sq z R ρ φ m
    nlinarith [(dist_nonneg : 0 ≤ dist (z + R • direction α) (z + ρ • direction m)),
      (dist_nonneg : 0 ≤ dist (z + R • direction φ) (z + ρ • direction m))]
  refine ⟨distinct, ⟨_, first, _, second, distinct, tied, nearest⟩, ⟨tied, nearest⟩, ?_⟩
  intro s hs not_first not_second
  obtain ⟨φ, interval, position⟩ := empty_gap s hs
  have lower : β < φ := lt_of_le_of_ne interval.1 (by
    intro same
    exact not_second (by simpa [← same] using position))
  have upper : φ < α + 2 * π := lt_of_le_of_ne interval.2 (by
    intro same
    exact not_first (by simpa [same, direction_add_two_pi] using position))
  have cosine : cos (m - φ) < cos δ := by
    rw [show m - φ = -(φ - m) by ring, cos_neg]
    exact cos_lt_away delta_positive.le (by dsimp [δ, m]; linarith)
      (by dsimp [δ, m]; linarith)
  have scaled := mul_lt_mul_of_pos_left cosine (show 0 < 2 * R * ρ by positivity)
  have left := circle_distance_sq z R ρ α m
  rw [cosine_p] at left
  have right := circle_distance_sq z R ρ φ m
  rw [position]
  change dist (z + R • direction α) (z + ρ • direction m) < _
  nlinarith [(dist_nonneg : 0 ≤ dist (z + R • direction α) (z + ρ • direction m)),
    (dist_nonneg : 0 ≤ dist (z + R • direction φ) (z + ρ • direction m))]

private theorem closer_of_larger_cosine (z : Plane) {R ρ α β φ : ℝ}
    (radius_positive : 0 < R) (sample_positive : 0 < ρ)
    (cosine : cos (φ - β) < cos (φ - α)) :
    dist (z + R • direction α) (z + ρ • direction φ) <
      dist (z + R • direction β) (z + ρ • direction φ) := by
  have scaled := mul_lt_mul_of_pos_left cosine (show 0 < 2 * R * ρ by positivity)
  have left := circle_distance_sq z R ρ α φ
  have right := circle_distance_sq z R ρ β φ
  nlinarith [(dist_nonneg : 0 ≤ dist (z + R • direction α) (z + ρ • direction φ)),
    (dist_nonneg : 0 ≤ dist (z + R • direction β) (z + ρ • direction φ))]

/-- Before the midpoint of an empty gap, its first endpoint is uniquely nearest. -/
private theorem gap_first_nearest (sources : Set Plane) (z : Plane) {R ρ α β φ : ℝ}
    (radius_positive : 0 < R) (sample_positive : 0 < ρ)
    (after_first : α ≤ φ) (before_midpoint : φ < (α + β) / 2)
    (empty_gap : ∀ p ∈ sources, ∃ η ∈ Icc β (α + 2 * π), p = z + R • direction η) :
    ∀ s ∈ sources, s ≠ z + R • direction α →
      dist (z + R • direction α) (z + ρ • direction φ) < dist s (z + ρ • direction φ) := by
  intro s hs different
  obtain ⟨η, interval, position⟩ := empty_gap s hs
  have upper : η < α + 2 * π := lt_of_le_of_ne interval.2 (by
    intro same
    exact different (by simpa [same, direction_add_two_pi] using position))
  rw [position]
  apply closer_of_larger_cosine z radius_positive sample_positive
  rw [show φ - η = -(η - φ) by ring, cos_neg]
  exact cos_lt_away (sub_nonneg.mpr after_first) (by linarith [interval.1]) (by linarith)

/-- After the midpoint of an empty gap, its second endpoint is uniquely nearest. -/
private theorem gap_second_nearest (sources : Set Plane) (z : Plane) {R ρ α β φ : ℝ}
    (radius_positive : 0 < R) (sample_positive : 0 < ρ)
    (after_midpoint : (α + β) / 2 < φ) (before_second : φ ≤ β)
    (empty_gap : ∀ p ∈ sources, ∃ η ∈ Icc β (α + 2 * π), p = z + R • direction η) :
    ∀ s ∈ sources, s ≠ z + R • direction β →
      dist (z + R • direction β) (z + ρ • direction φ) < dist s (z + ρ • direction φ) := by
  intro s hs different
  obtain ⟨η, interval, position⟩ := empty_gap s hs
  have lower : β < η := lt_of_le_of_ne interval.1 (by
    intro same
    exact different (by simpa [← same] using position))
  rw [position]
  apply closer_of_larger_cosine z radius_positive sample_positive
  rw [show φ - η = -(η - φ) by ring, show φ - β = -(β - φ) by ring, cos_neg, cos_neg]
  exact cos_lt_away (sub_nonneg.mpr before_second) (by linarith) (by linarith [interval.2])

private theorem not_boundary_of_strict_nearest {sources : Set Plane} {p x : Plane}
    (member : p ∈ sources) (nearest : ∀ s ∈ sources, s ≠ p → dist p x < dist s x) :
    x ∉ voronoiBoundary sources := by
  rintro ⟨q, hq, r, hr, different, tied, lower⟩
  have same : q = p := by
    by_contra unequal
    exact (not_le_of_gt (nearest q hq unequal)) (lower p member)
  subst q
  exact (ne_of_lt (nearest r hr (Ne.symm different))) tied

/-- Throughout a closed source gap, only its midpoint direction is a cut direction. -/
theorem circular_gap_boundary_iff (sources : Set Plane) (z : Plane) {R ρ α β φ : ℝ}
    (radius_positive : 0 < R) (sample_positive : 0 < ρ)
    (ordered : α < β) (one_turn : β < α + 2 * π)
    (first : z + R • direction α ∈ sources) (second : z + R • direction β ∈ sources)
    (empty_gap : ∀ p ∈ sources, ∃ η ∈ Icc β (α + 2 * π), p = z + R • direction η)
    (in_gap : φ ∈ Icc α β) :
    z + ρ • direction φ ∈ voronoiBoundary sources ↔ φ = (α + β) / 2 := by
  constructor
  · intro cut
    by_contra different
    rcases lt_or_gt_of_ne different with before | after
    · exact not_boundary_of_strict_nearest first
        (gap_first_nearest sources z radius_positive sample_positive in_gap.1 before empty_gap) cut
    · exact not_boundary_of_strict_nearest second
        (gap_second_nearest sources z radius_positive sample_positive after in_gap.2 empty_gap) cut
  · rintro rfl
    exact (circular_gap_voronoi_ray sources z radius_positive sample_positive ordered one_turn
      first second empty_gap).2.1

end SixVertexUnfolding
