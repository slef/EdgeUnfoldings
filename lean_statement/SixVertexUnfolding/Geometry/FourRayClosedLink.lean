import SixVertexUnfolding.Geometry.FourRayBoundaryLink
import SixVertexUnfolding.Geometry.QuadrilateralSplit

/-! The strict half-perimeter bound holds for every direction in the closed vertex figure. -/

namespace SixVertexUnfolding.FourRayFan

open InnerProductGeometry

variable (fan : FourRayFan)

/-- Interior directions of either diagonal triangle are no farther than its opposite boundary side. -/
theorem triangle_link_bound {p : Space}
    (member : p ∈ convexHull ℝ ({fan.ray 0, fan.ray 1, fan.ray 2} : Set Space)) :
    2 * angle (fan.ray 0) p < angle (fan.ray 0) (fan.ray 1) + angle (fan.ray 1) (fan.ray 2) +
      angle (fan.ray 2) (fan.ray 3) + angle (fan.ray 3) (fan.ray 0) := by
  have in_hull : p ∈ convexHull ℝ (Set.range fan.ray) := by
    apply convexHull_mono _ member
    rintro x (rfl | rfl | rfl)
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]
  have level := fan.hull_height in_hull
  have nonzero : p ≠ 0 := by intro zero; rw [zero, map_zero] at level; norm_num at level
  rw [convexHull_insert (Set.insert_nonempty (fan.ray 1) {fan.ray 2}), convexHull_pair] at member
  obtain ⟨a, ha, x, on_side, between⟩ := mem_convexJoin.mp member
  have same : a = fan.ray 0 := ha
  subst a
  have angle_sum := angle_add_of_segment (fan.ray 0) x p nonzero between
  have boundary := fan.boundary_link_bound on_side
  linarith [angle_nonneg p x]

/-- The strict closed-link bound includes boundary points and flat auxiliary corners. -/
theorem closed_link_bound {p : Space} (member : p ∈ convexHull ℝ (Set.range fan.ray)) :
    2 * angle (fan.ray 0) p < angle (fan.ray 0) (fan.ray 1) + angle (fan.ray 1) (fan.ray 2) +
      angle (fan.ray 2) (fan.ray 3) + angle (fan.ray 3) (fan.ray 0) := by
  have points : Set.range fan.ray = ({fan.ray 0, fan.ray 1, fan.ray 2, fan.ray 3} : Set Space) := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl | rfl | rfl)
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩]
  obtain ⟨x, first, second⟩ := fan.diagonals_meet
  rw [points, quadrilateral_split _ _ _ _ x first second] at member
  rcases member with first_triangle | second_triangle
  · exact fan.triangle_link_bound first_triangle
  · have reflected : p ∈ convexHull ℝ ({fan.reverse.ray 0, fan.reverse.ray 1, fan.reverse.ray 2} : Set Space) := by
      change p ∈ convexHull ℝ ({fan.ray 0, fan.ray 3, fan.ray 2} : Set Space)
      have reorder : ({fan.ray 0, fan.ray 3, fan.ray 2} : Set Space) = {fan.ray 0, fan.ray 2, fan.ray 3} := by
        ext z
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        tauto
      rwa [reorder]
    have bound := fan.reverse.triangle_link_bound reflected
    change 2 * angle (fan.ray 0) p < angle (fan.ray 0) (fan.ray 3) + angle (fan.ray 3) (fan.ray 2) +
      angle (fan.ray 2) (fan.ray 1) + angle (fan.ray 1) (fan.ray 0) at bound
    rw [angle_comm (fan.ray 0) (fan.ray 3), angle_comm (fan.ray 3) (fan.ray 2),
      angle_comm (fan.ray 2) (fan.ray 1), angle_comm (fan.ray 1) (fan.ray 0)] at bound
    linarith

/-- Sum notation for the closed-link bound based at the first ray. -/
theorem closed_link_bound_sum {p : Space} (member : p ∈ convexHull ℝ (Set.range fan.ray)) :
    2 * angle (fan.ray 0) p < ∑ i : Fin 4, angle (fan.ray i) (fan.ray (i + 1)) := by
  simpa only [Fin.sum_univ_four] using fan.closed_link_bound member

/-- The same strict bound holds from any of the four original or auxiliary incident rays. -/
theorem closed_link_bound_from (i : Fin 4) {p : Space}
    (member : p ∈ convexHull ℝ (Set.range fan.ray)) :
    2 * angle (fan.ray i) p < ∑ j : Fin 4, angle (fan.ray j) (fan.ray (j + 1)) := by
  have shifted : Function.Surjective (fun j : Fin 4 => i + j) := fun j => ⟨j - i, by simp⟩
  have points : Set.range (fan.rotate i).ray = Set.range fan.ray := by
    change Set.range (fan.ray ∘ (fun j => i + j)) = Set.range fan.ray
    rw [Set.range_comp, shifted.range_eq, Set.image_univ]
  have same_sum : (∑ j : Fin 4, angle ((fan.rotate i).ray j) ((fan.rotate i).ray (j + 1))) =
      ∑ j : Fin 4, angle (fan.ray j) (fan.ray (j + 1)) := by
    fin_cases i <;> simp [rotate, Fin.sum_univ_four] <;> ring
  have bound := (fan.rotate i).closed_link_bound_sum (by rwa [points])
  rw [same_sum] at bound
  simpa only [rotate, add_zero] using bound

end SixVertexUnfolding.FourRayFan
