import SixVertexUnfolding.Geometry.FourRayDiagonals

/-! The supported vertex figure has exactly the expected side intersections,
including when one corner is a flat subdivision point. -/

namespace SixVertexUnfolding

open Set

/-- Overlapping segments with a common start have comparable endpoints. -/
theorem segment_endpoints_comparable {o a b x : Space}
    (first : x ∈ segment ℝ o a) (second : x ∈ segment ℝ o b) (nonstart : x ≠ o) :
    a ∈ segment ℝ o b ∨ b ∈ segment ℝ o a := by
  obtain ⟨r, hr, er⟩ := (mem_segment_iff_wbtw.mp first).right_mem_image_Ici_of_left_ne nonstart.symm
  obtain ⟨s, hs, es⟩ := (mem_segment_iff_wbtw.mp second).right_mem_image_Ici_of_left_ne nonstart.symm
  change 1 ≤ r at hr
  change 1 ≤ s at hs
  rw [← er, ← es]
  simp only [AffineMap.lineMap_apply]
  rcases wbtw_or_wbtw_smul_vadd_of_nonneg o (x - o)
      (show 0 ≤ r by linarith) (show 0 ≤ s by linarith) with h | h
  · exact Or.inl h.mem_segment
  · exact Or.inr h.mem_segment

namespace FourRayFan

variable (fan : FourRayFan)

/-- Consecutive sides meet only at their common corner. -/
theorem adjacent_sides_intersection :
    segment ℝ (fan.ray 0) (fan.ray 1) ∩ segment ℝ (fan.ray 1) (fan.ray 2) =
      {fan.ray 1} := by
  apply Set.Subset.antisymm
  · rintro x ⟨first, second⟩
    by_contra different
    have nonstart : x ≠ fan.ray 1 := different
    rw [segment_symm] at first
    rcases segment_endpoints_comparable first second nonstart with h | h
    · have disjoint := (fan.rotate 3).opposite_sides_disjoint
      change Disjoint (segment ℝ (fan.ray 3) (fan.ray 0))
        (segment ℝ (fan.ray 1) (fan.ray 2)) at disjoint
      exact Set.disjoint_left.mp disjoint (right_mem_segment ℝ _ _) h
    · exact Set.disjoint_left.mp fan.opposite_sides_disjoint
        (by rwa [segment_symm]) (left_mem_segment ℝ _ _)
  · rintro x rfl
    exact ⟨right_mem_segment ℝ _ _, left_mem_segment ℝ _ _⟩

/-- A point common to two different sides is a shared endpoint of those sides. -/
theorem common_side_point (i j : Fin 4) (different : i ≠ j) {x : Space}
    (first : x ∈ segment ℝ (fan.ray i) (fan.ray (i + 1)))
    (second : x ∈ segment ℝ (fan.ray j) (fan.ray (j + 1))) :
    (j = i + 1 ∧ x = fan.ray (i + 1)) ∨ (i = j + 1 ∧ x = fan.ray i) := by
  have adjacent (k : Fin 4) :
      segment ℝ (fan.ray k) (fan.ray (k + 1)) ∩
        segment ℝ (fan.ray (k + 1)) (fan.ray (k + 2)) = {fan.ray (k + 1)} :=
    by simpa only [rotate, add_zero] using (fan.rotate k).adjacent_sides_intersection
  have opposite (k : Fin 4) : Disjoint
      (segment ℝ (fan.ray k) (fan.ray (k + 1)))
      (segment ℝ (fan.ray (k + 2)) (fan.ray (k + 3))) :=
    by simpa only [rotate, add_zero] using (fan.rotate k).opposite_sides_disjoint
  have options : j = i + 1 ∨ j = i + 2 ∨ i = j + 1 := by
    revert different
    fin_cases i <;> fin_cases j <;> decide
  rcases options with next | across | previous
  · refine Or.inl ⟨next, ?_⟩
    have pair : x ∈ segment ℝ (fan.ray i) (fan.ray (i + 1)) ∩
        segment ℝ (fan.ray (i + 1)) (fan.ray (i + 2)) := by
      refine ⟨first, ?_⟩
      simpa only [next, add_assoc, show (1 : Fin 4) + 1 = 2 from rfl] using second
    rwa [adjacent i] at pair
  · apply False.elim
    apply Set.disjoint_left.mp (opposite i) first
    simpa only [across, add_assoc, show (2 : Fin 4) + 1 = 3 from rfl] using second
  · refine Or.inr ⟨previous, ?_⟩
    have pair : x ∈ segment ℝ (fan.ray j) (fan.ray (j + 1)) ∩
        segment ℝ (fan.ray (j + 1)) (fan.ray (j + 2)) := by
      refine ⟨second, ?_⟩
      simpa only [previous, add_assoc, show (1 : Fin 4) + 1 = 2 from rfl] using first
    rw [adjacent j] at pair
    simpa only [previous] using pair

end FourRayFan
end SixVertexUnfolding
