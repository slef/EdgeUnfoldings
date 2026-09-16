import SixVertexUnfolding.Geometry.OctahedralLocalBoundary

/-! A remote petal can reach the opposite finite slit only across the gap and from a reflex near corner. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open Real EuclideanGeometry OctahedralTriangles

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

theorem patch_inward_at_left (i : Fin 4) (corner : (net.patch i).leftCorner ≤ π) :
    ∀ x ∈ (net.patch i).hull, 0 ≤ det (direction (graph.openingAngle (opposite source) slit i.castSucc)) x := by
  let θ := graph.openingAngle (opposite source) slit i.castSucc
  have at_left : det (direction θ) (net.patch i).left = 0 := by
    rw [net.patch_left]
    change det (direction θ) (_ • direction θ) = 0
    rw [det_smul_right, det_self, mul_zero]
  have at_right : 0 ≤ det (direction θ) (net.patch i).right := by
    rw [net.patch_right]
    change 0 ≤ det (direction θ) (_ • direction (graph.openingAngle (opposite source) slit i.succ))
    rw [det_smul_right, direction_det]
    change 0 ≤ _ * sin (graph.openingAngle (opposite source) slit i.succ - graph.openingAngle (opposite source) slit i.castSucc)
    rw [graph.openingAngle_step]
    exact mul_nonneg dist_nonneg (sin_pos_of_pos_of_lt_pi (graph.fanAngle_pos _ _) (graph.fanAngle_lt_pi _ _)).le
  have at_apex : 0 ≤ det (direction θ) (net.patch i).apex := by
    have expression : (net.patch i).apex = (net.patch i).left + ((net.patch i).apex - (net.patch i).left) := by module
    rw [expression, det_add_right, at_left, zero_add, net.patch_apex_direction_left, det_smul_right, direction_det]
    apply mul_nonneg dist_nonneg
    apply sin_nonneg_of_nonneg_of_le_pi <;> dsimp [θ] <;> linarith [(net.patch i).leftCorner_pos]
  let height := detHeight (direction θ)
  change (net.patch i).hull ⊆ {x | 0 ≤ height x}
  apply convexHull_min _ ((convex_Ici (0 : ℝ)).linear_preimage height.toLinearMap)
  rintro x (rfl | rfl | rfl | rfl)
  · rw [net.patch_pole]; simp [height, det]
  · exact at_left.ge
  · exact at_right
  · exact at_apex

/-- Any closed remote contact is on the across-gap angular branch; no generic-position assumption is used. -/
theorem first_remote_contact_across_gap
    (alternative : π ≤ graph.curvature source ∨ graph.curvature (opposite source) ≤ π)
    (x : Plane) (petal : x ∈ net.placedTriangle (true, 1))
    (contact : x ∈ segment ℝ 0 (net.patch 3).right) :
    π < graph.totalAngleAt (opposite source) - graph.openingAngle (opposite source) slit 1 := by
  have nonzero : x ≠ 0 := fun same => net.zero_not_mem_petal 1 (same ▸ petal)
  have span := (net.patch 1).angular_span_bound small_faces alternative (net.patch 1).left x
    (net.patch_left_mem_hull 1) (net.placedTriangle_subset_patch_hull true 1 petal)
    (by rw [net.patch_pole]; exact net.patch_left_ne_zero 1) (by rwa [net.patch_pole])
  rw [net.patch_pole, angle_eq_of_mem_radial_segment _ _ x contact nonzero,
    net.patch_left, net.patch_right] at span
  change 2 * angle (graph.openingPoint (opposite source) slit 1) 0
    (graph.openingPoint (opposite source) slit 4) < graph.totalAngleAt (opposite source) at span
  have first_bound := ((net.patch 0).corner_angle_bounds small_faces alternative).1
  rw [net.patch_fan_pole_angle] at first_bound
  change 2 * (graph.openingAngle (opposite source) slit 1 - 0) < _ at first_bound
  by_contra not_wide
  rw [graph.openingPoint_angle (opposite source) slit 1 4
    (by rw [graph.openingAngle_last]; linarith [graph.openingAngle_le_total (opposite source) slit 1])
    (by rw [graph.openingAngle_last]; exact le_of_not_gt not_wide), graph.openingAngle_last] at span
  linarith

/-- The half-fan estimate forces the first remote petal's near corner to be reflex whenever it contacts the opposite slit. -/
theorem first_remote_contact_forces_reflex
    (alternative : π ≤ graph.curvature source ∨ graph.curvature (opposite source) ≤ π)
    (x : Plane) (petal : x ∈ net.placedTriangle (true, 1))
    (contact : x ∈ segment ℝ 0 (net.patch 3).right) : π < (net.patch 1).leftCorner := by
  have wide := net.first_remote_contact_across_gap alternative x petal contact
  have upper : graph.totalAngleAt (opposite source) - graph.openingAngle (opposite source) slit 1 < 2 * π := by
    linarith [graph.totalAngleAt_lt_two_pi small_faces (opposite source), graph.openingAngle_nonneg (opposite source) slit 1]
  have endpoint : 0 < (-detHeight (direction (graph.openingAngle (opposite source) slit 1))) (net.patch 3).right := by
    change 0 < -det (direction (graph.openingAngle (opposite source) slit 1)) (net.patch 3).right
    rw [net.last_slit_position_total, det_smul_right, direction_det]
    have sine := sin_pos_of_pos_of_lt_pi
      (show 0 < graph.totalAngleAt (opposite source) - graph.openingAngle (opposite source) slit 1 - π by linarith)
      (show graph.totalAngleAt (opposite source) - graph.openingAngle (opposite source) slit 1 - π < π by linarith)
    rw [sin_sub_pi] at sine
    have product := mul_neg_of_pos_of_neg net.slitRadius_pos (neg_pos.mp sine)
    linarith
  have nonzero : x ≠ 0 := fun same => net.zero_not_mem_petal 1 (same ▸ petal)
  have negative := radial_segment_height_pos (-detHeight (direction (graph.openingAngle (opposite source) slit 1))).toLinearMap
    _ x endpoint contact nonzero
  by_contra not_reflex
  have positive := net.patch_inward_at_left 1 (le_of_not_gt not_reflex) x (net.placedTriangle_subset_patch_hull true 1 petal)
  change 0 ≤ det (direction (graph.openingAngle (opposite source) slit 1)) x at positive
  change 0 < -det (direction (graph.openingAngle (opposite source) slit 1)) x at negative
  linarith

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
