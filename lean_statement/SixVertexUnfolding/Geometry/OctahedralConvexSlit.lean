import SixVertexUnfolding.Geometry.SectorFlanks
import SixVertexUnfolding.Geometry.OctahedralPatchRayExclusion

/-! The local slit lemma when neither flank extends reflexly across the slit. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open Real EuclideanGeometry OctahedralTriangles

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

theorem last_slit_position_total : (net.patch 3).right =
    net.slitRadius • direction (graph.totalAngleAt (opposite source)) := by
  have total : graph.totalAngleAt (opposite source) = 2 * π - graph.curvature (opposite source) := by
    unfold curvature
    ring
  rw [total, direction_two_pi_sub]
  exact net.last_slit_position

/-- A nonreflex first slit corner keeps the entire first patch above its slit ray. -/
theorem first_patch_inward (nonreflex : (net.patch 0).leftCorner ≤ π) :
    ∀ x ∈ (net.patch 0).hull, 0 ≤ det (direction 0) x := by
  have at_left : det (direction 0) (net.patch 0).left = 0 := by
    rw [net.first_slit_position, det_smul_right, det_self, mul_zero]
  have at_right : 0 ≤ det (direction 0) (net.patch 0).right := by
    rw [net.patch_right]
    change 0 ≤ det (direction 0) (_ • direction (graph.openingAngle (opposite source) slit 1))
    rw [det_smul_right, direction_det]
    change 0 ≤ _ * sin (graph.fanAngle (opposite source) slit - 0)
    rw [sub_zero]
    exact mul_nonneg dist_nonneg (sin_pos_of_pos_of_lt_pi (graph.fanAngle_pos _ _) (graph.fanAngle_lt_pi _ _)).le
  have at_apex : 0 ≤ det (direction 0) (net.patch 0).apex := by
    have vector := net.patch_apex_direction_left 0
    change (net.patch 0).apex - (net.patch 0).left = _ • direction (0 + π - (net.patch 0).leftCorner) at vector
    have expression : (net.patch 0).apex = (net.patch 0).left + ((net.patch 0).apex - (net.patch 0).left) := by module
    rw [expression, det_add_right, at_left, zero_add, vector, det_smul_right, direction_det]
    exact mul_nonneg dist_nonneg (sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [(net.patch 0).leftCorner_pos]))
  let height := detHeight (direction 0)
  change (net.patch 0).hull ⊆ {x | 0 ≤ height x}
  unfold DevelopedPatch.hull
  apply convexHull_min _ ((convex_Ici (0 : ℝ)).linear_preimage height.toLinearMap)
  rintro x (rfl | rfl | rfl | rfl)
  · rw [net.patch_pole]; simp [height, det]
  · exact at_left.ge
  · exact at_right
  · exact at_apex

/-- A nonreflex last slit corner keeps its entire patch below the last slit ray. -/
theorem last_patch_inward (nonreflex : (net.patch 3).rightCorner ≤ π) :
    ∀ x ∈ (net.patch 3).hull, det (direction (graph.totalAngleAt (opposite source))) x ≤ 0 := by
  let Γ := graph.totalAngleAt (opposite source)
  have at_right : det (direction Γ) (net.patch 3).right = 0 := by
    rw [net.last_slit_position_total, det_smul_right]
    change net.slitRadius * det (direction Γ) (direction Γ) = 0
    rw [det_self, mul_zero]
  have at_left : det (direction Γ) (net.patch 3).left ≤ 0 := by
    rw [net.patch_left]
    change det (direction Γ) (_ • direction (graph.openingAngle (opposite source) slit 3)) ≤ 0
    rw [det_smul_right, direction_det]
    apply mul_nonpos_of_nonneg_of_nonpos dist_nonneg
    have step := graph.openingAngle_step (opposite source) slit 3
    change graph.openingAngle (opposite source) slit 4 - graph.openingAngle (opposite source) slit 3 = _ at step
    rw [graph.openingAngle_last] at step
    have positive := graph.fanAngle_pos (opposite source) (slit + 3)
    have small := graph.fanAngle_lt_pi (opposite source) (slit + 3)
    apply sin_nonpos_of_nonpos_of_neg_pi_le <;> dsimp [Γ] <;> linarith
  have at_apex : det (direction Γ) (net.patch 3).apex ≤ 0 := by
    have vector := net.patch_apex_direction_right 3
    change (net.patch 3).apex - (net.patch 3).right = _ • direction
      (graph.openingAngle (opposite source) slit 4 - π + (net.patch 3).rightCorner) at vector
    rw [graph.openingAngle_last] at vector
    have expression : (net.patch 3).apex = (net.patch 3).right + ((net.patch 3).apex - (net.patch 3).right) := by module
    rw [expression, det_add_right, at_right, zero_add, vector, det_smul_right, direction_det]
    apply mul_nonpos_of_nonneg_of_nonpos dist_nonneg
    apply sin_nonpos_of_nonpos_of_neg_pi_le <;> dsimp [Γ] <;> linarith [(net.patch 3).rightCorner_pos]
  let height := detHeight (direction Γ)
  change (net.patch 3).hull ⊆ {x | height x ≤ 0}
  unfold DevelopedPatch.hull
  apply convexHull_min _ ((convex_Iic (0 : ℝ)).linear_preimage height.toLinearMap)
  rintro x (rfl | rfl | rfl | rfl)
  · rw [net.patch_pole]; simp [height, det]
  · exact at_left
  · exact at_right.le
  · exact at_apex

/-- Inward side conditions and strict half-fan spans exclude any nonzero common point. -/
theorem slit_patches_meet_only_at_zero_of_sides
    (alternative : π ≤ graph.curvature source ∨ graph.curvature (opposite source) ≤ π)
    (x : Plane) (first : x ∈ (net.patch 0).hull) (last : x ∈ (net.patch 3).hull)
    (first_side : 0 ≤ det (direction 0) x)
    (last_side : det (direction (graph.totalAngleAt (opposite source))) x ≤ 0) : x = 0 := by
  by_contra nonzero
  have first_span := (net.patch 0).angular_span_bound small_faces alternative (net.patch 0).left x
    (net.patch_left_mem_hull 0) first (by rw [net.patch_pole]; exact net.patch_left_ne_zero 0)
    (by rwa [net.patch_pole])
  have last_span := (net.patch 3).angular_span_bound small_faces alternative x (net.patch 3).right
    last (net.patch_right_mem_hull 3) (by rwa [net.patch_pole])
    (by rw [net.patch_pole]; exact net.patch_right_ne_zero 3)
  rw [net.patch_pole, net.first_slit_position] at first_span
  rw [net.patch_pole, net.last_slit_position_total] at last_span
  exact inward_flanks_cannot_meet net.slitRadius net.slitRadius (graph.totalAngleAt (opposite source))
    net.slitRadius_pos net.slitRadius_pos (graph.totalAngleAt_pos _) (graph.totalAngleAt_lt_two_pi small_faces _)
    x nonzero first_side last_side
    first_span last_span

/-- Strict half-fan bounds and nonreflex slit corners separate the two whole patch hulls. -/
theorem convex_slit_patches_meet_only_at_zero
    (alternative : π ≤ graph.curvature source ∨ graph.curvature (opposite source) ≤ π)
    (first_corner : (net.patch 0).leftCorner ≤ π) (last_corner : (net.patch 3).rightCorner ≤ π)
    (x : Plane) (first : x ∈ (net.patch 0).hull) (last : x ∈ (net.patch 3).hull) : x = 0 :=
  net.slit_patches_meet_only_at_zero_of_sides alternative x first last
    (net.first_patch_inward first_corner x first) (net.last_patch_inward last_corner x last)

/-- All three local pairs are safe when both slit corners are nonreflex, including straight corners. -/
theorem local_pairs_of_nonreflex_slit
    (alternative : π ≤ graph.curvature source ∨ graph.curvature (opposite source) ≤ π)
    (first_corner : (net.patch 0).leftCorner ≤ π) (last_corner : (net.patch 3).rightCorner ≤ π) : net.LocalPairs := by
  have safe (petal : Bool) : net.Separated (true, 0) (petal, 3) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    have zero := net.convex_slit_patches_meet_only_at_zero alternative first_corner last_corner x
      (net.placedTriangle_subset_patch_hull true 0 (interior_subset hx))
      (net.placedTriangle_subset_patch_hull petal 3 (interior_subset hy))
    exact net.zero_not_mem_petal 0 (zero ▸ interior_subset hx)
  refine ⟨safe true, safe false, ?_⟩
  apply Set.disjoint_left.mpr
  intro x hx hy
  have zero := net.convex_slit_patches_meet_only_at_zero alternative first_corner last_corner x
    (net.placedTriangle_subset_patch_hull false 0 (interior_subset hy))
    (net.placedTriangle_subset_patch_hull true 3 (interior_subset hx))
  exact net.zero_not_mem_petal 3 (zero ▸ interior_subset hx)

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
