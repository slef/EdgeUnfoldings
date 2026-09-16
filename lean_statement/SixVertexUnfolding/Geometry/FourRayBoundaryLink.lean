import SixVertexUnfolding.Geometry.FourRayPerimeter
import SixVertexUnfolding.Geometry.FourRayReverse
import SixVertexUnfolding.Geometry.SphericalSpan

/-! Each boundary direction is strictly closer than half the vertex-figure angular perimeter. -/

namespace SixVertexUnfolding.FourRayFan

open InnerProductGeometry

variable (fan : FourRayFan)

/-- Every ray endpoint is nonzero, since it lies at transverse height one. -/
theorem ray_ne_zero (i : Fin 4) : fan.ray i ≠ 0 := by
  intro zero
  have level := fan.level i
  rw [zero, map_zero] at level
  norm_num at level

/-- The entire convex vertex figure lies at the same transverse height. -/
theorem hull_height {x : Space} (member : x ∈ convexHull ℝ (Set.range fan.ray)) : fan.height x = 1 := by
  have constant : Set.EqOn fan.height.toAffineMap (AffineMap.const ℝ Space (1 : ℝ)) (Set.range fan.ray) := by
    rintro y ⟨i, rfl⟩
    exact fan.level i
  exact AffineMap.eqOn_affineSpan constant (convexHull_subset_affineSpan _ member)

/-- A point of any side segment is nonzero and has height one. -/
theorem segment_height (i j : Fin 4) {x : Space} (member : x ∈ segment ℝ (fan.ray i) (fan.ray j)) :
    fan.height x = 1 := by
  obtain ⟨a, b, _, _, total, combination⟩ := member
  rw [← combination, map_add, map_smul, map_smul, fan.level, fan.level]
  simpa only [smul_eq_mul, mul_one] using total

/-- Neither of the two boundary paths can attain equality simultaneously: that would flatten all four rays. -/
theorem boundary_link_bound {x : Space} (member : x ∈ segment ℝ (fan.ray 1) (fan.ray 2)) :
    2 * angle (fan.ray 0) x < angle (fan.ray 0) (fan.ray 1) + angle (fan.ray 1) (fan.ray 2) +
      angle (fan.ray 2) (fan.ray 3) + angle (fan.ray 3) (fan.ray 0) := by
  have xheight : fan.height x = 1 := fan.segment_height 1 2 member
  have xpos : 0 < fan.height x := by rw [xheight]; norm_num
  have xnonzero : x ≠ 0 := by intro zero; rw [zero, map_zero] at xheight; norm_num at xheight
  have positive (i : Fin 4) : 0 < fan.height (fan.ray i) := by rw [fan.level]; norm_num
  have split := angle_add_of_segment (fan.ray 1) (fan.ray 2) x xnonzero member
  have first := angle_le_angle_add_angle (fan.ray 0) (fan.ray 1) x
  have second := angle_le_angle_add_angle (fan.ray 0) (fan.ray 3) x
  have third := angle_le_angle_add_angle (fan.ray 3) (fan.ray 2) x
  have dc := angle_comm (fan.ray 3) (fan.ray 2)
  have da := angle_comm (fan.ray 3) (fan.ray 0)
  have cx := angle_comm (fan.ray 2) x
  by_contra not_strict
  have bound := le_of_not_gt not_strict
  have first_equal : angle (fan.ray 0) x = angle (fan.ray 0) (fan.ray 1) + angle (fan.ray 1) x := by linarith
  have second_equal : angle (fan.ray 0) x = angle (fan.ray 0) (fan.ray 3) + angle (fan.ray 3) x := by linarith
  have third_equal : angle (fan.ray 3) x = angle (fan.ray 3) (fan.ray 2) + angle (fan.ray 2) x := by linarith
  let S := Submodule.span ℝ ({fan.ray 0, x} : Set Space)
  have aS : fan.ray 0 ∈ S := Submodule.subset_span (by simp)
  have xS : x ∈ S := Submodule.subset_span (by simp)
  have bS := angle_add_mem_subspace fan.height S (fan.ray 0) (fan.ray 1) x
    (positive 0) xpos (fan.ray_ne_zero 1) aS xS first_equal
  have dS := angle_add_mem_subspace fan.height S (fan.ray 0) (fan.ray 3) x
    (positive 0) xpos (fan.ray_ne_zero 3) aS xS second_equal
  have cS := angle_add_mem_subspace fan.height S (fan.ray 3) (fan.ray 2) x
    (positive 3) xpos (fan.ray_ne_zero 2) dS xS third_equal
  apply fan.not_contained_in_pair_span (fan.ray 0) x
  intro i
  fin_cases i
  exacts [aS, bS, cS, dS]

end SixVertexUnfolding.FourRayFan
