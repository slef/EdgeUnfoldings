import SixVertexUnfolding.Geometry.OctahedralShortReflexHeight
import SixVertexUnfolding.Geometry.OctahedralHighFan

/-! Reflex slit flanks that do not cross the curvature gap are safe on either side. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open Real EuclideanGeometry OctahedralTriangles

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

theorem first_short_reflex_patches_meet_only_at_zero
    (alternative : π ≤ graph.curvature source ∨ graph.curvature (opposite source) ≤ π)
    (ρ : ℝ) (positive : 0 < ρ) (reflex : (net.patch 0).leftCorner = π + ρ)
    (short : ρ ≤ graph.curvature (opposite source))
    (x : Plane) (first : x ∈ (net.patch 0).hull) (last : x ∈ (net.patch 3).hull) : x = 0 := by
  by_cases high : π ≤ graph.curvature (opposite source)
  · exact net.high_fan_first_last_meet_only_at_zero alternative high x first last
  by_contra nonzero
  have corners := net.slit_corner_sum
  have total_small := graph.totalAngleAt_lt_two_pi small_faces (fanNeighbor source slit)
  rw [reflex] at corners
  have last_corner : (net.patch 3).rightCorner ≤ π := by linarith
  have last_side := net.last_patch_inward last_corner x last
  by_cases first_side : 0 ≤ det (direction 0) x
  · exact nonzero (net.slit_patches_meet_only_at_zero_of_sides alternative x first last first_side last_side)
  · have direction_eq : direction (graph.totalAngleAt (opposite source)) = direction (-graph.curvature (opposite source)) := by
      rw [show graph.totalAngleAt (opposite source) = 2 * π - graph.curvature (opposite source) by unfold curvature; ring,
        direction_two_pi_sub]
    rw [direction_eq] at last_side
    exact short_gap_before (graph.curvature (opposite source)) ρ (graph.curvature_pos small_faces _)
      (lt_of_not_ge high) positive short x (lt_of_not_ge first_side)
      (net.first_reflex_outer_height ρ positive reflex x first nonzero) last_side

theorem last_short_reflex_patches_meet_only_at_zero
    (alternative : π ≤ graph.curvature source ∨ graph.curvature (opposite source) ≤ π)
    (ρ : ℝ) (positive : 0 < ρ) (reflex : (net.patch 3).rightCorner = π + ρ)
    (short : ρ ≤ graph.curvature (opposite source))
    (x : Plane) (first : x ∈ (net.patch 0).hull) (last : x ∈ (net.patch 3).hull) : x = 0 := by
  by_cases high : π ≤ graph.curvature (opposite source)
  · exact net.high_fan_first_last_meet_only_at_zero alternative high x first last
  by_contra nonzero
  have corners := net.slit_corner_sum
  have total_small := graph.totalAngleAt_lt_two_pi small_faces (fanNeighbor source slit)
  rw [reflex] at corners
  have first_corner : (net.patch 0).leftCorner ≤ π := by linarith
  have first_side := net.first_patch_inward first_corner x first
  by_cases last_side : det (direction (graph.totalAngleAt (opposite source))) x ≤ 0
  · exact nonzero (net.slit_patches_meet_only_at_zero_of_sides alternative x first last first_side last_side)
  · apply short_gap_after (graph.totalAngleAt (opposite source)) (graph.curvature (opposite source)) ρ
      (graph.curvature_pos small_faces _) (lt_of_not_ge high) positive short x (lt_of_not_ge last_side)
      (net.last_reflex_outer_height ρ positive reflex x last nonzero)
    rw [show graph.totalAngleAt (opposite source) + graph.curvature (opposite source) = 0 + 2 * π by unfold curvature; ring,
      direction_add_two_pi]
    exact first_side

/-- Once the two closed flank hulls meet only at the pole, all three local pairs follow. -/
theorem local_pairs_of_flank_intersection
    (meet : ∀ x : Plane, x ∈ (net.patch 0).hull → x ∈ (net.patch 3).hull → x = 0) : net.LocalPairs := by
  have safe (petal : Bool) : net.Separated (true, 0) (petal, 3) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    have zero := meet x (net.placedTriangle_subset_patch_hull true 0 (interior_subset hx))
      (net.placedTriangle_subset_patch_hull petal 3 (interior_subset hy))
    exact net.zero_not_mem_petal 0 (zero ▸ interior_subset hx)
  refine ⟨safe true, safe false, ?_⟩
  apply Set.disjoint_left.mpr
  intro x hx hy
  have zero := meet x (net.placedTriangle_subset_patch_hull false 0 (interior_subset hy))
    (net.placedTriangle_subset_patch_hull true 3 (interior_subset hx))
  exact net.zero_not_mem_petal 3 (zero ▸ interior_subset hx)

/-- This includes nonreflex corners and equality when a reflex corner equals pi plus the curvature gap. -/
theorem local_pairs_of_corners_within_gap
    (alternative : π ≤ graph.curvature source ∨ graph.curvature (opposite source) ≤ π)
    (first_corner : (net.patch 0).leftCorner ≤ π + graph.curvature (opposite source))
    (last_corner : (net.patch 3).rightCorner ≤ π + graph.curvature (opposite source)) : net.LocalPairs := by
  by_cases first_convex : (net.patch 0).leftCorner ≤ π
  · by_cases last_convex : (net.patch 3).rightCorner ≤ π
    · exact net.local_pairs_of_nonreflex_slit alternative first_convex last_convex
    · apply net.local_pairs_of_flank_intersection
      exact net.last_short_reflex_patches_meet_only_at_zero alternative ((net.patch 3).rightCorner - π)
        (by linarith) (by ring) (by linarith)
  · apply net.local_pairs_of_flank_intersection
    exact net.first_short_reflex_patches_meet_only_at_zero alternative ((net.patch 0).leftCorner - π)
      (by linarith) (by ring) (by linarith)

/-- The sole local branch not yet included here is a last-flank corner crossing the gap. -/
theorem local_pairs_unless_last_corner_crosses_gap
    (alternative : π ≤ graph.curvature source ∨ graph.curvature (opposite source) ≤ π)
    (threshold : π ≤ 2 * graph.curvature (fanNeighbor source slit) + graph.curvature (opposite source))
    (last_corner : (net.patch 3).rightCorner ≤ π + graph.curvature (opposite source)) : net.LocalPairs := by
  by_cases first_corner : (net.patch 0).leftCorner ≤ π + graph.curvature (opposite source)
  · exact net.local_pairs_of_corners_within_gap alternative first_corner last_corner
  · exact net.local_pairs_of_first_corner_crosses_gap (lt_of_not_ge first_corner) threshold

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
