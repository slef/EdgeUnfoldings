import SixVertexUnfolding.Geometry.FourRayFan

/-! The opposite diagonals of a supported four-corner vertex figure must meet. -/

namespace SixVertexUnfolding.FourRayFan

variable (fan : FourRayFan)

/-- A supporting side vanishes along its whole closed side segment. -/
theorem side_zero_on_segment (i : Fin 4) {x : Space}
    (member : x ∈ segment ℝ (fan.ray i) (fan.ray (i + 1))) : fan.side i x = 0 := by
  obtain ⟨a, b, _, _, _, combination⟩ := member
  rw [← combination, map_add, map_smul, map_smul, fan.side_left, fan.side_right]
  simp

/-- An interior point with zero supporting height forces both endpoint heights to vanish. -/
theorem endpoints_zero (i j k : Fin 4) {x : Space} (zero : fan.side i x = 0)
    (middle : x ∈ openSegment ℝ (fan.ray j) (fan.ray k)) :
    fan.side i (fan.ray j) = 0 ∧ fan.side i (fan.ray k) = 0 := by
  obtain ⟨a, b, ha, hb, _, combination⟩ := middle
  have equation := congrArg (fan.side i) combination
  simp only [map_add, map_smul, smul_eq_mul, zero] at equation
  constructor
  · nlinarith [fan.side_bound i j, mul_nonpos_of_nonneg_of_nonpos hb.le (fan.side_bound i k)]
  · nlinarith [fan.side_bound i k, mul_nonpos_of_nonneg_of_nonpos ha.le (fan.side_bound i j)]

/-- A nonzero side cannot vanish on all four spanning rays. -/
theorem not_zero_at_four (i : Fin 4) (h0 : fan.side i (fan.ray 0) = 0)
    (h1 : fan.side i (fan.ray 1) = 0) (h2 : fan.side i (fan.ray 2) = 0)
    (h3 : fan.side i (fan.ray 3) = 0) : False := by
  obtain ⟨j, negative⟩ := fan.side_has_negative i
  fin_cases j
  exacts [(not_lt_of_ge h0.ge negative), (not_lt_of_ge h1.ge negative),
    (not_lt_of_ge h2.ge negative), (not_lt_of_ge h3.ge negative)]

/-- Two opposite supporting sides cannot intersect, even at a flat subdivision corner. -/
theorem opposite_sides_disjoint :
    Disjoint (segment ℝ (fan.ray 0) (fan.ray 1)) (segment ℝ (fan.ray 2) (fan.ray 3)) := by
  apply Set.disjoint_left.mpr
  intro x left right
  have left_zero := fan.side_zero_on_segment 0 left
  have right_zero := fan.side_zero_on_segment 2 right
  have finish_right (not2 : fan.ray 2 ≠ x) (not3 : fan.ray 3 ≠ x) : False := by
    have middle := mem_openSegment_of_ne_left_right not2 not3 right
    obtain ⟨h2, h3⟩ := fan.endpoints_zero 0 2 3 left_zero middle
    exact fan.not_zero_at_four 0 (fan.side_left 0) (fan.side_right 0) h2 h3
  by_cases at0 : fan.ray 0 = x
  · apply finish_right
    · exact fun same => (by decide : (2 : Fin 4) ≠ 0) (fan.distinct (same.trans at0.symm))
    · exact fun same => (by decide : (3 : Fin 4) ≠ 0) (fan.distinct (same.trans at0.symm))
  by_cases at1 : fan.ray 1 = x
  · apply finish_right
    · exact fun same => (by decide : (2 : Fin 4) ≠ 1) (fan.distinct (same.trans at1.symm))
    · exact fun same => (by decide : (3 : Fin 4) ≠ 1) (fan.distinct (same.trans at1.symm))
  obtain ⟨h0, h1⟩ := fan.endpoints_zero 2 0 1 right_zero
    (mem_openSegment_of_ne_left_right at0 at1 left)
  exact fan.not_zero_at_four 2 h0 h1 (fan.side_left 2) (fan.side_right 2)

/-- The eight Radon parts containing label zero. -/
def radonParts : Fin 8 → Finset (Fin 4) :=
  ![{0}, {0, 1}, {0, 2}, {0, 3}, {0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {0, 1, 2, 3}]

def radonOthers : Fin 8 → Finset (Fin 4) :=
  ![{1, 2, 3}, {2, 3}, {1, 3}, {1, 2}, {3}, {2}, {1}, ∅]

theorem radonParts_exhaust : ∀ part : Finset (Fin 4), 0 ∈ part → ∃ k, part = radonParts k := by decide

theorem radonParts_compl : ∀ k, (radonParts k)ᶜ = radonOthers k := by decide

/-- The two closed diagonals intersect, with endpoint contact allowed at a flat corner. -/
theorem diagonals_meet : ∃ x, x ∈ segment ℝ (fan.ray 0) (fan.ray 2) ∧
    x ∈ segment ℝ (fan.ray 1) (fan.ray 3) := by
  classical
  obtain ⟨part, x, first, second⟩ := Convex.radon_partition fan.affinely_dependent
  have partition : ∃ part : Set (Fin 4), 0 ∈ part ∧
      x ∈ convexHull ℝ (fan.ray '' part) ∧ x ∈ convexHull ℝ (fan.ray '' partᶜ) := by
    by_cases contains : 0 ∈ part
    · exact ⟨part, contains, first, second⟩
    · exact ⟨partᶜ, contains, second, by simpa only [compl_compl] using first⟩
  obtain ⟨part, zero, first, second⟩ := partition
  obtain ⟨k, selected⟩ := radonParts_exhaust part.toFinite.toFinset (by simpa using zero)
  have part_eq : part = (radonParts k : Set (Fin 4)) := by rw [← selected]; simp
  have other_eq : partᶜ = (radonOthers k : Set (Fin 4)) := by
    rw [part_eq, ← Finset.coe_compl, radonParts_compl]
  rw [part_eq] at first
  rw [other_eq] at second
  fin_cases k
  · have own : x = fan.ray 0 := by simpa [radonParts] using first
    subst x
    have flat := fan.corner_in_neighbors (by simpa [radonOthers, Set.image_insert_eq, Set.image_singleton] using second)
    exact ⟨fan.ray 0, left_mem_segment ℝ _ _, flat⟩
  · have left : x ∈ segment ℝ (fan.ray 0) (fan.ray 1) := by
      simpa [radonParts, Set.image_insert_eq, Set.image_singleton, convexHull_pair] using first
    have right : x ∈ segment ℝ (fan.ray 2) (fan.ray 3) := by
      simpa [radonOthers, Set.image_insert_eq, Set.image_singleton, convexHull_pair] using second
    exact (Set.disjoint_left.mp fan.opposite_sides_disjoint left right).elim
  · refine ⟨x, ?_, ?_⟩
    · simpa [radonParts, Set.image_insert_eq, Set.image_singleton, convexHull_pair] using first
    · simpa [radonOthers, Set.image_insert_eq, Set.image_singleton, convexHull_pair] using second
  · have left : x ∈ segment ℝ ((fan.rotate 3).ray 0) ((fan.rotate 3).ray 1) := by
      change x ∈ segment ℝ (fan.ray 3) (fan.ray 0)
      rw [segment_symm]
      simpa [radonParts, Set.image_insert_eq, Set.image_singleton, convexHull_pair] using first
    have right : x ∈ segment ℝ ((fan.rotate 3).ray 2) ((fan.rotate 3).ray 3) := by
      change x ∈ segment ℝ (fan.ray 1) (fan.ray 2)
      simpa [radonOthers, Set.image_insert_eq, Set.image_singleton, convexHull_pair] using second
    exact (Set.disjoint_left.mp (fan.rotate 3).opposite_sides_disjoint left right).elim
  · have own : x = fan.ray 3 := by simpa [radonOthers] using second
    subst x
    have member : (fan.rotate 3).ray 0 ∈ convexHull ℝ
        ({(fan.rotate 3).ray 1, (fan.rotate 3).ray 2, (fan.rotate 3).ray 3} : Set Space) := by
      change fan.ray 3 ∈ convexHull ℝ ({fan.ray 0, fan.ray 1, fan.ray 2} : Set Space)
      simpa [radonParts, Set.image_insert_eq, Set.image_singleton] using first
    exact ⟨fan.ray 3, (fan.rotate 3).corner_in_neighbors member, right_mem_segment ℝ _ _⟩
  · have own : x = fan.ray 2 := by simpa [radonOthers] using second
    subst x
    have member : (fan.rotate 2).ray 0 ∈ convexHull ℝ
        ({(fan.rotate 2).ray 1, (fan.rotate 2).ray 2, (fan.rotate 2).ray 3} : Set Space) := by
      change fan.ray 2 ∈ convexHull ℝ ({fan.ray 3, fan.ray 0, fan.ray 1} : Set Space)
      have reorder : ({fan.ray 0, fan.ray 1, fan.ray 3} : Set Space) = {fan.ray 3, fan.ray 0, fan.ray 1} := by
        ext z
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        tauto
      rw [← reorder]
      simpa [radonParts, Set.image_insert_eq, Set.image_singleton] using first
    have flat : fan.ray 2 ∈ segment ℝ (fan.ray 3) (fan.ray 1) := (fan.rotate 2).corner_in_neighbors member
    exact ⟨fan.ray 2, right_mem_segment ℝ _ _, by rwa [segment_symm]⟩
  · have own : x = fan.ray 1 := by simpa [radonOthers] using second
    subst x
    have member : (fan.rotate 1).ray 0 ∈ convexHull ℝ
        ({(fan.rotate 1).ray 1, (fan.rotate 1).ray 2, (fan.rotate 1).ray 3} : Set Space) := by
      change fan.ray 1 ∈ convexHull ℝ ({fan.ray 2, fan.ray 3, fan.ray 0} : Set Space)
      have reorder : ({fan.ray 0, fan.ray 2, fan.ray 3} : Set Space) = {fan.ray 2, fan.ray 3, fan.ray 0} := by
        ext z
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        tauto
      rw [← reorder]
      simpa [radonParts, Set.image_insert_eq, Set.image_singleton] using first
    have flat : fan.ray 1 ∈ segment ℝ (fan.ray 2) (fan.ray 0) := (fan.rotate 1).corner_in_neighbors member
    exact ⟨fan.ray 1, by rwa [segment_symm], left_mem_segment ℝ _ _⟩
  · simp [radonOthers] at second

end SixVertexUnfolding.FourRayFan
