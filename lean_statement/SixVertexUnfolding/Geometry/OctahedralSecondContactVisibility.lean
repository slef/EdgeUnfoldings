import SixVertexUnfolding.Geometry.OctahedralSecondContactContainment
import SixVertexUnfolding.Geometry.OctahedralApexGap
import SixVertexUnfolding.Geometry.ReflexRadialTriangleRight
import SixVertexUnfolding.Geometry.RayTriangleEntry

/-! Whole second-remote-petal contact reaches its copied right cut edge. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open Real EuclideanGeometry OctahedralTriangles

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

theorem second_remote_reflex_sides (reflex : π < (net.patch 2).rightCorner) :
    det (net.patch 2).right (net.patch 2).left < 0 ∧
    0 < det (net.patch 2).right (net.patch 2).apex := by
  let θ := graph.openingAngle (opposite source) slit 3
  have fan : det (net.patch 2).right (net.patch 2).left < 0 := by
    rw [det_swap]
    apply neg_neg_of_pos
    rw [net.patch_left, net.patch_right]
    change 0 < det (_ • direction (graph.openingAngle (opposite source) slit 2))
      (_ • direction (graph.openingAngle (opposite source) slit 3))
    rw [det_smul_left, det_smul_right, direction_det]
    have step := graph.openingAngle_step (opposite source) slit 2
    change graph.openingAngle (opposite source) slit 3 - graph.openingAngle (opposite source) slit 2 = _ at step
    rw [step]
    exact mul_pos (graph.opening_radius_pos _ _ _) (mul_pos (graph.opening_radius_pos _ _ _)
      (sin_pos_of_pos_of_lt_pi (graph.fanAngle_pos _ _) (graph.fanAngle_lt_pi _ _)))
  have corner_upper : (net.patch 2).rightCorner < 2 * π := by
    have sum := net.junction_corner_sum 2
    have bound := graph.totalAngleAt_lt_two_pi small_faces (fanNeighbor source ((slit + 2) + 1))
    change (net.patch 2).rightCorner + (net.patch 3).leftCorner =
      graph.totalAngleAt (fanNeighbor source ((slit + 2) + 1)) at sum
    linarith [(net.patch 3).leftCorner_pos]
  have right_zero : det (direction θ) (net.patch 2).right = 0 := by
    rw [net.patch_right]
    change det (direction θ) (_ • direction θ) = 0
    rw [det_smul_right, det_self, mul_zero]
  have apex_positive : 0 < det (direction θ) (net.patch 2).apex := by
    have position : (net.patch 2).apex = (net.patch 2).right + ((net.patch 2).apex - (net.patch 2).right) := by module
    rw [position, det_add_right, right_zero, zero_add, net.patch_apex_direction_right, det_smul_right, direction_det]
    apply mul_pos (dist_pos.mpr (net.petal_apex_ne_right 2))
    change 0 < sin (θ - π + (net.patch 2).rightCorner - θ)
    apply sin_pos_of_pos_of_lt_pi <;> linarith
  refine ⟨fan, ?_⟩
  rw [net.patch_right]
  change 0 < det (_ • direction θ) (net.patch 2).apex
  rw [det_smul_left]
  exact mul_pos (graph.opening_radius_pos _ _ _) apex_positive

/-- Closed finite contact reaches the copied edge at the second remote petal's reflex right corner. -/
theorem second_remote_contact_reaches_cut
    (alternative : π ≤ graph.curvature source ∨ graph.curvature (opposite source) ≤ π)
    (x : Plane) (petal : x ∈ net.placedTriangle (true, 2))
    (contact : x ∈ segment ℝ 0 (net.patch 0).left) :
    ∃ y : Plane, y ≠ 0 ∧ y ∈ segment ℝ 0 (net.patch 0).left ∧
      y ∈ segment ℝ (net.patch 2).right (net.patch 2).apex := by
  have reflex := net.second_remote_contact_forces_reflex alternative x petal contact
  obtain ⟨fan_side, reflex_side⟩ := net.second_remote_reflex_sides reflex
  have noncollinear : ¬ Collinear ℝ ({(net.patch 2).right, (net.patch 2).left, 0} : Set Plane) := by
    rw [Set.insert_comm]
    simpa only [net.patch_pole] using (net.patch 2).fan_noncollinear
  have outward : OppositeHingeSides (net.patch 2).right (net.patch 2).left 0 (net.patch 2).apex := by
    rw [oppositeHingeSides_swap _ _ _ _ (ne₁₂_of_not_collinear (net.patch 2).petal_noncollinear)]
    simpa only [net.patch_pole] using (net.patch 2).outward
  have near := near_vertex_in_radial_triangle_clockwise (net.patch 2).right (net.patch 2).left (net.patch 2).apex
    fan_side reflex_side noncollinear outward
  have off_ray (b : Plane) (area : det (net.patch 2).right b ≠ 0) : (net.patch 2).right ∉ segment ℝ 0 b := by
    rintro ⟨s, t, _, _, _, position⟩
    apply area
    rw [← position]
    simp only [smul_zero, zero_add, det_smul_left, det_self, mul_zero]
  have hinge_clear : Disjoint (segment ℝ (net.patch 2).right (net.patch 2).left)
      (segment ℝ 0 (net.patch 0).left) := by
    apply Set.disjoint_left.mpr
    intro y hinge on_slit
    have in_fan := (net.placedTriangle_convex (false, 2)).segment_subset
      (net.patch_right_mem false 2) (net.patch_left_mem false 2) hinge
    have in_first := (net.placedTriangle_convex (false, 0)).segment_subset
      (net.fan_pole_mem 0) (net.patch_left_mem false 0) on_slit
    have zero := net.opposite_fan_pair_meet_only_at_zero 2 y in_fan in_first
    have in_petal := (net.placedTriangle_convex (true, 2)).segment_subset
      (net.patch_right_mem true 2) (net.patch_left_mem true 2) hinge
    exact net.zero_not_mem_petal 2 (zero ▸ in_petal)
  apply finite_ray_contact_reaches_cut_edge _ _ _ _ x near
    (off_ray _ fan_side.ne) (off_ray _ reflex_side.ne') _ contact
    (fun zero => net.zero_not_mem_petal 2 (zero ▸ petal)) hinge_clear
  rw [Set.insert_comm]
  simpa only [net.placedTriangle_hull, Bool.true_eq, ite_true] using petal

/-- The second whole remote petal misses the first closed slit at a high-curvature source. -/
theorem second_remote_cut_clear_of_high_source (source_high : π ≤ graph.curvature source)
    (threshold : π ≤ 2 * graph.curvature (fanNeighbor source slit) + graph.curvature (opposite source)) :
    Disjoint (net.placedTriangle (true, 2)) (segment ℝ 0 (net.patch 0).left) := by
  apply Set.disjoint_left.mpr
  intro x petal contact
  have reflex := net.second_remote_contact_forces_reflex (Or.inl source_high) x petal contact
  obtain ⟨y, _, on_slit, on_cut⟩ := net.second_remote_contact_reaches_cut (Or.inl source_high) x petal contact
  have right_clear : (net.patch 2).right ∉ segment ℝ 0 (net.patch 0).left := by
    intro hit
    have in_first := (net.placedTriangle_convex (false, 0)).segment_subset
      (net.fan_pole_mem 0) (net.patch_left_mem false 0) hit
    have zero := net.opposite_fan_pair_meet_only_at_zero 2 (net.patch 2).right
      (net.patch_right_mem false 2) in_first
    exact net.patch_right_ne_zero 2 zero
  obtain ⟨s, t, hs, ht, sum, position⟩ := on_cut
  have positive : 0 < t := by
    apply lt_of_le_of_ne ht
    intro zero
    have vanish : t = 0 := zero.symm
    have one : s = 1 := by linarith
    have same : (net.patch 2).right = y := by simpa only [vanish, one, one_smul, zero_smul, add_zero] using position
    exact right_clear (same ▸ on_slit)
  have parameter : (net.patch 2).right + t • ((net.patch 2).apex - (net.patch 2).right) = y := by
    rw [← position, show s = 1 - t by linarith]
    module
  have impossible := net.source_curvature_lt_pi_of_second_cut_contact (Or.inl source_high) threshold reflex t positive
    (show t ≤ 1 by linarith) (by rwa [parameter])
  linarith

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
