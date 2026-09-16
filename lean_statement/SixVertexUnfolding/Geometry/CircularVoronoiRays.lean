import SixVertexUnfolding.Geometry.CircularVoronoiSectors

/-! The complete Voronoi boundary for source copies on a common circle:
the center and exactly the rays bisecting consecutive angular gaps.
-/

namespace SixVertexUnfolding

open Real Set

/-- Directions bisecting consecutive gaps, with the closing gap written explicitly. -/
def circularGapMidpoints {n : ℕ} (θ : Fin n → ℝ) (first last : Fin n) : Set ℝ :=
  {m | (∃ i j : Fin n, j.val = i.val + 1 ∧ m = (θ i + θ j) / 2) ∨
    m = (θ last + (θ first + 2 * π)) / 2}

/-- The list of gap directions is finite. -/
theorem circularGapMidpoints_finite {n : ℕ} (θ : Fin n → ℝ) (first last : Fin n) :
    (circularGapMidpoints θ first last).Finite := by
  have pairs := finite_range (fun p : Fin n × Fin n => (θ p.1 + θ p.2) / 2)
  apply (pairs.union (finite_singleton ((θ last + (θ first + 2 * π)) / 2))).subset
  rintro m (⟨i, j, _, rfl⟩ | rfl)
  · exact Or.inl ⟨(i, j), rfl⟩
  · exact Or.inr rfl

/-- All gap midpoints lie strictly within one full turn from the first source. -/
theorem circular_midpoint_bounds {n : ℕ} (θ : Fin n → ℝ) (increasing : StrictMono θ)
    (bounds : ∀ i, 0 ≤ θ i ∧ θ i < 2 * π) (first last : Fin n) (at_first : first.val = 0)
    {m : ℝ} (midpoint : m ∈ circularGapMidpoints θ first last) :
    θ first < m ∧ m < θ first + 2 * π := by
  rcases midpoint with ⟨i, j, next, rfl⟩ | rfl
  · have order := increasing (show i < j by omega)
    have lower := increasing.monotone (show first ≤ i by omega)
    constructor <;> linarith [(bounds i).2, (bounds j).2, (bounds first).1]
  · have order := increasing.monotone (show first ≤ last by omega)
    constructor <;> linarith [(bounds last).2, (bounds first).1, pi_pos]

/-- Two listed positive rays can meet only if both their directions and radii agree. -/
theorem circular_gap_ray_unique {n : ℕ} (θ : Fin n → ℝ) (increasing : StrictMono θ)
    (bounds : ∀ i, 0 ≤ θ i ∧ θ i < 2 * π) (first last : Fin n) (at_first : first.val = 0)
    (z : Plane) {m k ρ σ : ℝ} (hm : m ∈ circularGapMidpoints θ first last)
    (hk : k ∈ circularGapMidpoints θ first last) (rp : 0 < ρ) (sp : 0 < σ)
    (same : z + ρ • direction m = z + σ • direction k) : m = k ∧ ρ = σ := by
  have bm := circular_midpoint_bounds θ increasing bounds first last at_first hm
  have bk := circular_midpoint_bounds θ increasing bounds first last at_first hk
  have vectors := add_left_cancel same
  have angles := polar_angle_eq_of_one_turn ρ σ m k rp sp (by linarith) (by linarith) vectors
  have radii := congrArg (dist (0 : Plane)) vectors
  rw [polar_radius ρ m rp.le, polar_radius σ k sp.le] at radii
  exact ⟨angles, radii⟩

/-- Every listed gap midpoint gives a nearest-source tie at every positive radius. -/
theorem circular_midpoint_is_boundary {sources : Set Plane} {n : ℕ} (e : Fin n ≃ sources)
    (θ : Fin n → ℝ) (increasing : StrictMono θ) (bounds : ∀ i, 0 ≤ θ i ∧ θ i < 2 * π)
    (z : Plane) {R : ℝ} (radius_positive : 0 < R)
    (position : ∀ i, (e i : Plane) = z + R • direction (θ i))
    (first last : Fin n) (at_first : first.val = 0) (at_last : last.val + 1 = n)
    (two : first < last) {m ρ : ℝ} (midpoint : m ∈ circularGapMidpoints θ first last)
    (sample_positive : 0 < ρ) : z + ρ • direction m ∈ voronoiBoundary sources := by
  rcases midpoint with ⟨i, j, next, rfl⟩ | rfl
  · exact (circular_gap_voronoi_ray sources z radius_positive sample_positive
      (increasing (by omega)) (by linarith [(bounds i).1, (bounds j).2])
      (position i ▸ (e i).property) (position j ▸ (e j).property)
      (circular_order_gap e θ increasing bounds z R position i j next)).2.1
  · have first_mem : z + R • direction (θ first + 2 * π) ∈ sources := by
      rw [direction_add_two_pi]
      exact position first ▸ (e first).property
    exact (circular_gap_voronoi_ray sources z radius_positive sample_positive
      (show θ last < θ first + 2 * π by linarith [(bounds last).2, (bounds first).1])
      (show θ first + 2 * π < θ last + 2 * π by linarith [increasing two])
      (position last ▸ (e last).property) first_mem
      (closing_circular_order_gap e θ increasing z R position first last at_first at_last)).2.1

/-- There are no additional cut directions between or beyond the listed gap rays. -/
theorem circular_boundary_on_listed_ray {sources : Set Plane} {n : ℕ} (e : Fin n ≃ sources)
    (θ : Fin n → ℝ) (increasing : StrictMono θ) (bounds : ∀ i, 0 ≤ θ i ∧ θ i < 2 * π)
    (z : Plane) {R : ℝ} (radius_positive : 0 < R)
    (position : ∀ i, (e i : Plane) = z + R • direction (θ i))
    (first last : Fin n) (at_first : first.val = 0) (at_last : last.val + 1 = n)
    (two : first < last) {x : Plane} (not_center : x ≠ z) (cut : x ∈ voronoiBoundary sources) :
    ∃ (ρ : ℝ), 0 < ρ ∧ ∃ m ∈ circularGapMidpoints θ first last, x = z + ρ • direction m := by
  let ρ := dist x z
  have positive : 0 < ρ := dist_pos.mpr not_center
  obtain ⟨φ, low, high, coordinates⟩ := circle_point_angle positive (show dist x z = ρ from rfl)
  rcases circular_gaps_cover_direction θ increasing bounds first last ⟨low, high⟩ with
    ⟨i, j, next, in_gap⟩ | ⟨ψ, in_gap, same_direction⟩
  · have criterion := circular_gap_boundary_iff sources z radius_positive positive
      (increasing (by omega)) (by linarith [(bounds i).1, (bounds j).2])
      (position i ▸ (e i).property) (position j ▸ (e j).property)
      (circular_order_gap e θ increasing bounds z R position i j next) in_gap
    have midpoint := criterion.mp (coordinates ▸ cut)
    exact ⟨ρ, positive, φ, Or.inl ⟨i, j, next, midpoint⟩, coordinates⟩
  · have first_mem : z + R • direction (θ first + 2 * π) ∈ sources := by
      rw [direction_add_two_pi]
      exact position first ▸ (e first).property
    have criterion := circular_gap_boundary_iff sources z radius_positive positive
      (show θ last < θ first + 2 * π by linarith [(bounds last).2, (bounds first).1])
      (show θ first + 2 * π < θ last + 2 * π by linarith [increasing two])
      (position last ▸ (e last).property) first_mem
      (closing_circular_order_gap e θ increasing z R position first last at_first at_last) in_gap
    have representation : x = z + ρ • direction ψ := coordinates.trans (by rw [same_direction])
    have midpoint := criterion.mp (representation ▸ cut)
    exact ⟨ρ, positive, ψ, Or.inr midpoint, representation⟩

/-- Exact equality of the whole diagram with the center and the listed positive rays. -/
theorem circular_voronoi_boundary_iff {sources : Set Plane} {n : ℕ} (e : Fin n ≃ sources)
    (θ : Fin n → ℝ) (increasing : StrictMono θ) (bounds : ∀ i, 0 ≤ θ i ∧ θ i < 2 * π)
    (z : Plane) {R : ℝ} (radius_positive : 0 < R)
    (position : ∀ i, (e i : Plane) = z + R • direction (θ i))
    (first last : Fin n) (at_first : first.val = 0) (at_last : last.val + 1 = n)
    (two : first < last) (x : Plane) :
    x ∈ voronoiBoundary sources ↔ x = z ∨
      ∃ (ρ : ℝ), 0 < ρ ∧ ∃ m ∈ circularGapMidpoints θ first last, x = z + ρ • direction m := by
  constructor
  · intro cut
    by_cases center : x = z
    · exact Or.inl center
    · exact Or.inr (circular_boundary_on_listed_ray e θ increasing bounds z radius_positive
        position first last at_first at_last two center cut)
  · rintro (center | ⟨ρ, positive, m, midpoint, same⟩)
    · rw [center]
      have common (p : sources) : dist (p : Plane) z = R := by
        obtain ⟨i, rfl⟩ := e.surjective p
        rw [position i, dist_eq_norm, add_sub_cancel_left, norm_smul, direction_norm, mul_one,
          Real.norm_eq_abs, abs_of_pos radius_positive]
      refine ⟨e first, (e first).property, e last, (e last).property, ?_,
        (common (e first)).trans (common (e last)).symm, ?_⟩
      · intro same
        exact (ne_of_lt two) (e.injective (Subtype.ext same))
      · intro p hp
        rw [common (e first), common ⟨p, hp⟩]
    · rw [same]
      exact circular_midpoint_is_boundary e θ increasing bounds z radius_positive position
        first last at_first at_last two midpoint positive

end SixVertexUnfolding
