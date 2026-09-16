import SixVertexUnfolding.Geometry.OctahedralContactEntry

/-! The second remote petal reaches the first slit only across the gap and from a reflex right corner. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open Real EuclideanGeometry OctahedralTriangles

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

theorem patch_inward_at_right (i : Fin 4) (corner : (net.patch i).rightCorner ≤ π) :
    ∀ x ∈ (net.patch i).hull, det (direction (graph.openingAngle (opposite source) slit i.succ)) x ≤ 0 := by
  let θ := graph.openingAngle (opposite source) slit i.succ
  have at_right : det (direction θ) (net.patch i).right = 0 := by
    rw [net.patch_right]
    change det (direction θ) (_ • direction θ) = 0
    rw [det_smul_right, det_self, mul_zero]
  have at_left : det (direction θ) (net.patch i).left ≤ 0 := by
    rw [net.patch_left]
    change det (direction θ) (_ • direction (graph.openingAngle (opposite source) slit i.castSucc)) ≤ 0
    rw [det_smul_right, direction_det]
    apply mul_nonpos_of_nonneg_of_nonpos dist_nonneg
    have step := graph.openingAngle_step (opposite source) slit i
    apply sin_nonpos_of_nonpos_of_neg_pi_le <;> dsimp [θ] <;>
      linarith [graph.fanAngle_pos (opposite source) (slit + i), graph.fanAngle_lt_pi (opposite source) (slit + i)]
  have at_apex : det (direction θ) (net.patch i).apex ≤ 0 := by
    have expression : (net.patch i).apex = (net.patch i).right + ((net.patch i).apex - (net.patch i).right) := by module
    rw [expression, det_add_right, at_right, zero_add, net.patch_apex_direction_right, det_smul_right, direction_det]
    apply mul_nonpos_of_nonneg_of_nonpos dist_nonneg
    apply sin_nonpos_of_nonpos_of_neg_pi_le <;> dsimp [θ] <;> linarith [(net.patch i).rightCorner_pos]
  let height := detHeight (direction θ)
  change (net.patch i).hull ⊆ {x | height x ≤ 0}
  apply convexHull_min _ ((convex_Iic (0 : ℝ)).linear_preimage height.toLinearMap)
  rintro x (rfl | rfl | rfl | rfl)
  · rw [net.patch_pole]; simp [height, det]
  · exact at_left
  · exact at_right.le
  · exact at_apex

/-- The contact lies on the long angular branch from the second remote petal's right endpoint. -/
theorem second_remote_contact_across_gap
    (alternative : π ≤ graph.curvature source ∨ graph.curvature (opposite source) ≤ π)
    (x : Plane) (petal : x ∈ net.placedTriangle (true, 2))
    (contact : x ∈ segment ℝ 0 (net.patch 0).left) :
    π < graph.openingAngle (opposite source) slit 3 := by
  have nonzero : x ≠ 0 := fun same => net.zero_not_mem_petal 2 (same ▸ petal)
  have span := (net.patch 2).angular_span_bound small_faces alternative (net.patch 2).right x
    (net.patch_right_mem_hull 2) (net.placedTriangle_subset_patch_hull true 2 petal)
    (by rw [net.patch_pole]; exact net.patch_right_ne_zero 2) (by rwa [net.patch_pole])
  rw [net.patch_pole, angle_eq_of_mem_radial_segment _ _ x contact nonzero,
    net.patch_right, net.patch_left, angle_comm] at span
  change 2 * angle (graph.openingPoint (opposite source) slit 0) 0
    (graph.openingPoint (opposite source) slit 3) < graph.totalAngleAt (opposite source) at span
  have last_bound := ((net.patch 3).corner_angle_bounds small_faces alternative).1
  rw [net.patch_fan_pole_angle] at last_bound
  change 2 * (graph.openingAngle (opposite source) slit 4 - graph.openingAngle (opposite source) slit 3) < _ at last_bound
  rw [graph.openingAngle_last] at last_bound
  by_contra not_wide
  rw [graph.openingPoint_angle (opposite source) slit 0 3
    (by change 0 ≤ _ - 0; simpa using graph.openingAngle_nonneg (opposite source) slit 3)
    (by change _ - 0 ≤ π; simpa using le_of_not_gt not_wide)] at span
  change 2 * (graph.openingAngle (opposite source) slit 3 - 0) < _ at span
  linarith

theorem second_remote_contact_forces_reflex
    (alternative : π ≤ graph.curvature source ∨ graph.curvature (opposite source) ≤ π)
    (x : Plane) (petal : x ∈ net.placedTriangle (true, 2))
    (contact : x ∈ segment ℝ 0 (net.patch 0).left) : π < (net.patch 2).rightCorner := by
  have wide := net.second_remote_contact_across_gap alternative x petal contact
  have upper : graph.openingAngle (opposite source) slit 3 < 2 * π :=
    (graph.openingAngle_le_total _ _ _).trans_lt (graph.totalAngleAt_lt_two_pi small_faces _)
  have endpoint : 0 < (detHeight (direction (graph.openingAngle (opposite source) slit 3))) (net.patch 0).left := by
    change 0 < det (direction (graph.openingAngle (opposite source) slit 3)) (net.patch 0).left
    rw [net.first_slit_position, det_smul_right, direction_det, zero_sub, sin_neg]
    have sine := sin_pos_of_pos_of_lt_pi
      (show 0 < graph.openingAngle (opposite source) slit 3 - π by linarith)
      (show graph.openingAngle (opposite source) slit 3 - π < π by linarith)
    rw [sin_sub_pi] at sine
    exact mul_pos net.slitRadius_pos sine
  have nonzero : x ≠ 0 := fun same => net.zero_not_mem_petal 2 (same ▸ petal)
  have positive := radial_segment_height_pos (detHeight (direction (graph.openingAngle (opposite source) slit 3))).toLinearMap
    _ x endpoint contact nonzero
  by_contra not_reflex
  have negative := net.patch_inward_at_right 2 (le_of_not_gt not_reflex) x (net.placedTriangle_subset_patch_hull true 2 petal)
  change det (direction (graph.openingAngle (opposite source) slit 3)) x ≤ 0 at negative
  change 0 < det (direction (graph.openingAngle (opposite source) slit 3)) x at positive
  linarith

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
