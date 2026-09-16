import SixVertexUnfolding.Geometry.OctahedralContactContainment
import SixVertexUnfolding.Geometry.OctahedralApexGap
import SixVertexUnfolding.Geometry.ReflexRadialTriangle
import SixVertexUnfolding.Geometry.RayTriangleEntry

/-! Whole remote-petal contact is reduced to contact on its copied cut edge. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open Real EuclideanGeometry OctahedralTriangles

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

theorem first_remote_reflex_sides (reflex : π < (net.patch 1).leftCorner) :
    0 < det (net.patch 1).left (net.patch 1).right ∧
    det (net.patch 1).left (net.patch 1).apex < 0 := by
  let θ := graph.openingAngle (opposite source) slit 1
  have fan : 0 < det (net.patch 1).left (net.patch 1).right := by
    rw [net.patch_left, net.patch_right]
    change 0 < det (_ • direction (graph.openingAngle (opposite source) slit 1))
      (_ • direction (graph.openingAngle (opposite source) slit 2))
    rw [det_smul_left, det_smul_right, direction_det]
    have step := graph.openingAngle_step (opposite source) slit 1
    change graph.openingAngle (opposite source) slit 2 - graph.openingAngle (opposite source) slit 1 = _ at step
    rw [step]
    exact mul_pos (graph.opening_radius_pos _ _ _) (mul_pos (graph.opening_radius_pos _ _ _)
      (sin_pos_of_pos_of_lt_pi (graph.fanAngle_pos _ _) (graph.fanAngle_lt_pi _ _)))
  have corner_upper : (net.patch 1).leftCorner < 2 * π := by
    have sum := net.junction_corner_sum 0
    have bound := graph.totalAngleAt_lt_two_pi small_faces (fanNeighbor source (slit + 1))
    change (net.patch 0).rightCorner + (net.patch 1).leftCorner =
      graph.totalAngleAt (fanNeighbor source ((slit + 0) + 1)) at sum
    simp only [add_zero] at sum
    linarith [(net.patch 0).rightCorner_pos]
  have left_zero : det (direction θ) (net.patch 1).left = 0 := by
    rw [net.patch_left]
    change det (direction θ) (_ • direction θ) = 0
    rw [det_smul_right, det_self, mul_zero]
  have apex_negative : det (direction θ) (net.patch 1).apex < 0 := by
    have position : (net.patch 1).apex = (net.patch 1).left + ((net.patch 1).apex - (net.patch 1).left) := by module
    rw [position, det_add_right, left_zero, zero_add, net.patch_apex_direction_left, det_smul_right, direction_det]
    have apex_ne : (net.patch 1).apex ≠ (net.patch 1).left :=
      (ne₁₃_of_not_collinear (net.patch 1).petal_noncollinear).symm
    apply mul_neg_of_pos_of_neg (dist_pos.mpr apex_ne)
    change sin (θ + π - (net.patch 1).leftCorner - θ) < 0
    rw [show θ + π - (net.patch 1).leftCorner - θ = -((net.patch 1).leftCorner - π) by ring, sin_neg]
    exact neg_neg_of_pos (sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
  refine ⟨fan, ?_⟩
  rw [net.patch_left]
  change det (_ • direction θ) (net.patch 1).apex < 0
  rw [det_smul_left]
  exact mul_neg_of_pos_of_neg (graph.opening_radius_pos _ _ _) apex_negative

/-- The whole closed petal reaches the opposite slit only through its copied near cut edge. -/
theorem first_remote_contact_reaches_cut
    (alternative : π ≤ graph.curvature source ∨ graph.curvature (opposite source) ≤ π)
    (x : Plane) (petal : x ∈ net.placedTriangle (true, 1))
    (contact : x ∈ segment ℝ 0 (net.patch 3).right) :
    ∃ y : Plane, y ≠ 0 ∧ y ∈ segment ℝ 0 (net.patch 3).right ∧
      y ∈ segment ℝ (net.patch 1).left (net.patch 1).apex := by
  have reflex := net.first_remote_contact_forces_reflex alternative x petal contact
  obtain ⟨fan_side, reflex_side⟩ := net.first_remote_reflex_sides reflex
  have near := near_vertex_in_radial_triangle (net.patch 1).left (net.patch 1).right (net.patch 1).apex
    fan_side reflex_side (by simpa only [net.patch_pole] using (net.patch 1).fan_noncollinear)
    (by simpa only [net.patch_pole] using (net.patch 1).outward)
  have off_ray (b : Plane) (area : det (net.patch 1).left b ≠ 0) : (net.patch 1).left ∉ segment ℝ 0 b := by
    rintro ⟨s, t, _, _, _, position⟩
    apply area
    rw [← position]
    simp only [smul_zero, zero_add, det_smul_left, det_self, mul_zero]
  have hinge_clear : Disjoint (segment ℝ (net.patch 1).left (net.patch 1).right)
      (segment ℝ 0 (net.patch 3).right) := by
    apply Set.disjoint_left.mpr
    intro y hinge on_slit
    have in_fan := (net.placedTriangle_convex (false, 1)).segment_subset
      (net.patch_left_mem false 1) (net.patch_right_mem false 1) hinge
    have in_last := (net.placedTriangle_convex (false, 3)).segment_subset
      (net.fan_pole_mem 3) (net.patch_right_mem false 3) on_slit
    have zero := net.opposite_fan_pair_meet_only_at_zero 1 y in_fan in_last
    have in_petal := (net.placedTriangle_convex (true, 1)).segment_subset
      (net.patch_left_mem true 1) (net.patch_right_mem true 1) hinge
    exact net.zero_not_mem_petal 1 (zero ▸ in_petal)
  apply finite_ray_contact_reaches_cut_edge _ _ _ _ x near
    (off_ray _ fan_side.ne') (off_ray _ reflex_side.ne) _ contact
    (fun zero => net.zero_not_mem_petal 1 (zero ▸ petal)) hinge_clear
  simpa only [net.placedTriangle_hull, Bool.true_eq, ite_true] using petal

/-- High source curvature rules out contact of the entire first remote petal with the opposite closed slit. -/
theorem first_remote_cut_clear_of_high_source (source_high : π ≤ graph.curvature source)
    (threshold : π ≤ 2 * graph.curvature (fanNeighbor source slit) + graph.curvature (opposite source)) :
    Disjoint (net.placedTriangle (true, 1)) (segment ℝ 0 (net.patch 3).right) := by
  apply Set.disjoint_left.mpr
  intro x petal contact
  obtain ⟨y, _, on_slit, on_cut⟩ := net.first_remote_contact_reaches_cut (Or.inl source_high) x petal contact
  have left_clear : (net.patch 1).left ∉ segment ℝ 0 (net.patch 3).right := by
    intro hit
    have in_last := (net.placedTriangle_convex (false, 3)).segment_subset
      (net.fan_pole_mem 3) (net.patch_right_mem false 3) hit
    have zero := net.opposite_fan_pair_meet_only_at_zero 1 (net.patch 1).left
      (net.patch_left_mem false 1) in_last
    exact net.patch_left_ne_zero 1 zero
  obtain ⟨s, t, hs, ht, sum, position⟩ := on_cut
  have positive : 0 < t := by
    apply lt_of_le_of_ne ht
    intro zero
    have vanish : t = 0 := zero.symm
    have one : s = 1 := by linarith
    have same : (net.patch 1).left = y := by simpa only [vanish, one, one_smul, zero_smul, add_zero] using position
    exact left_clear (same ▸ on_slit)
  have shared := net.consecutive_patch_corner 0
  change (net.patch 0).right = (net.patch 1).left at shared
  have parameter : (net.patch 0).right + t • ((net.patch 1).apex - (net.patch 0).right) = y := by
    rw [shared, ← position, show s = 1 - t by linarith]
    module
  apply net.first_cut_edge_cannot_reach_last_slit source_high threshold t positive (by linarith)
  rwa [parameter]

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
