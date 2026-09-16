import SixVertexUnfolding.Geometry.OctahedralLocal

/-! The local lemma also excludes closed contact of either flank petal with the opposite finite slit. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open Real OctahedralTriangles

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

theorem patch_left_segment_subset (i : Fin 4) : segment ℝ 0 (net.patch i).left ⊆ (net.patch i).hull := by
  apply (convex_convexHull ℝ _).segment_subset
  · apply subset_convexHull ℝ _
    rw [net.patch_pole]
    simp
  · exact net.patch_left_mem_hull i

theorem patch_right_segment_subset (i : Fin 4) : segment ℝ 0 (net.patch i).right ⊆ (net.patch i).hull := by
  apply (convex_convexHull ℝ _).segment_subset
  · apply subset_convexHull ℝ _
    rw [net.patch_pole]
    simp
  · exact net.patch_right_mem_hull i

theorem flank_cuts_of_patch_intersection
    (meet : ∀ x : Plane, x ∈ (net.patch 0).hull → x ∈ (net.patch 3).hull → x = 0) :
    Disjoint (net.placedTriangle (true, 0)) (segment ℝ 0 (net.patch 3).right) ∧
      Disjoint (net.placedTriangle (true, 3)) (segment ℝ 0 (net.patch 0).left) := by
  constructor
  · apply Set.disjoint_left.mpr
    intro x hx hy
    have zero := meet x (net.placedTriangle_subset_patch_hull true 0 hx) (net.patch_right_segment_subset 3 hy)
    exact net.zero_not_mem_petal 0 (zero ▸ hx)
  · apply Set.disjoint_left.mpr
    intro x hx hy
    have zero := meet x (net.patch_left_segment_subset 0 hy) (net.placedTriangle_subset_patch_hull true 3 hx)
    exact net.zero_not_mem_petal 3 (zero ▸ hx)

theorem first_inward_petal_misses_last_slit (gap_small : graph.curvature (opposite source) < π)
    (corner : (net.patch 0).leftCorner ≤ π) :
    Disjoint (net.placedTriangle (true, 0)) (segment ℝ 0 (net.patch 3).right) := by
  have endpoint : 0 < (-detHeight (direction 0)) (net.patch 3).right := by
    change 0 < -det (direction 0) (net.patch 3).right
    rw [net.last_slit_position, det_smul_right, direction_det, sub_zero, sin_neg]
    have positive := mul_pos net.slitRadius_pos (sin_pos_of_pos_of_lt_pi (graph.curvature_pos small_faces _) gap_small)
    nlinarith
  apply Set.disjoint_left.mpr
  intro x hx hy
  have nonzero : x ≠ 0 := fun same => net.zero_not_mem_petal 0 (same ▸ hx)
  have negative := radial_segment_height_pos (-detHeight (direction 0)).toLinearMap _ x endpoint hy nonzero
  have positive := net.first_patch_inward corner x (net.placedTriangle_subset_patch_hull true 0 hx)
  change 0 < -det (direction 0) x at negative
  linarith

theorem last_inward_petal_misses_first_slit (gap_small : graph.curvature (opposite source) < π)
    (corner : (net.patch 3).rightCorner ≤ π) :
    Disjoint (net.placedTriangle (true, 3)) (segment ℝ 0 (net.patch 0).left) := by
  let d := direction (graph.totalAngleAt (opposite source))
  have direction_eq : d = direction (-graph.curvature (opposite source)) := by
    change direction (graph.totalAngleAt (opposite source)) = _
    rw [show graph.totalAngleAt (opposite source) = 2 * π - graph.curvature (opposite source) by unfold curvature; ring,
      direction_two_pi_sub]
  have endpoint : 0 < detHeight d (net.patch 0).left := by
    rw [detHeight_apply, direction_eq, net.first_slit_position, det_smul_right, direction_det, zero_sub, neg_neg]
    exact mul_pos net.slitRadius_pos (sin_pos_of_pos_of_lt_pi (graph.curvature_pos small_faces _) gap_small)
  apply Set.disjoint_left.mpr
  intro x hx hy
  have nonzero : x ≠ 0 := fun same => net.zero_not_mem_petal 3 (same ▸ hx)
  have positive := radial_segment_height_pos (detHeight d).toLinearMap _ x endpoint hy nonzero
  have negative := net.last_patch_inward corner x (net.placedTriangle_subset_patch_hull true 3 hx)
  change 0 < det d x at positive
  exact (not_lt_of_ge negative) positive

/-- The closed flank petals miss the closed opposite slit segments, including all four endpoints. -/
theorem local_flank_cuts
    (alternative : π ≤ graph.curvature source ∨ graph.curvature (opposite source) ≤ π)
    (threshold : π ≤ 2 * graph.curvature (fanNeighbor source slit) + graph.curvature (opposite source)) :
    Disjoint (net.placedTriangle (true, 0)) (segment ℝ 0 (net.patch 3).right) ∧
      Disjoint (net.placedTriangle (true, 3)) (segment ℝ 0 (net.patch 0).left) := by
  have corners := net.slit_corner_sum
  have first_pos := (net.patch 0).leftCorner_pos
  have last_pos := (net.patch 3).rightCorner_pos
  have total_small := graph.totalAngleAt_lt_two_pi small_faces (fanNeighbor source slit)
  have gap_pos := graph.curvature_pos small_faces (opposite source)
  by_cases first_crosses : π + graph.curvature (opposite source) < (net.patch 0).leftCorner
  · exact ⟨(net.first_reflex_closed_separation ((net.patch 0).leftCorner - π) (by ring) (by linarith) threshold).2,
      net.last_inward_petal_misses_first_slit (by linarith) (by linarith)⟩
  by_cases last_crosses : π + graph.curvature (opposite source) < (net.patch 3).rightCorner
  · exact ⟨net.first_inward_petal_misses_last_slit (by linarith) (by linarith),
      (net.last_reflex_closed_separation ((net.patch 3).rightCorner - π) (by ring) (by linarith) threshold).2⟩
  apply net.flank_cuts_of_patch_intersection
  by_cases first_convex : (net.patch 0).leftCorner ≤ π
  · by_cases last_convex : (net.patch 3).rightCorner ≤ π
    · exact net.convex_slit_patches_meet_only_at_zero alternative first_convex last_convex
    · exact net.last_short_reflex_patches_meet_only_at_zero alternative ((net.patch 3).rightCorner - π)
        (by linarith) (by ring) (by linarith)
  · exact net.first_short_reflex_patches_meet_only_at_zero alternative ((net.patch 0).leftCorner - π)
      (by linarith) (by ring) (by linarith)

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
