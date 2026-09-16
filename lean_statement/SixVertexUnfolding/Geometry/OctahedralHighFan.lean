import SixVertexUnfolding.Geometry.OctahedralPatchRayExclusion

/-! When the fan angle sum is at most pi, half-fan bounds prove all local pairs and both finite-cut exclusions. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Real EuclideanGeometry OctahedralTriangles

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)

theorem openingPoint_angle (pole : Fin 6) (slit : Fin 4) (i j : Fin 5)
    (lower : 0 ≤ graph.openingAngle pole slit j - graph.openingAngle pole slit i)
    (upper : graph.openingAngle pole slit j - graph.openingAngle pole slit i ≤ π) :
    angle (graph.openingPoint pole slit i) 0 (graph.openingPoint pole slit j) =
      graph.openingAngle pole slit j - graph.openingAngle pole slit i :=
  radial_angle _ _ _ _ (graph.opening_radius_pos _ _ _) (graph.opening_radius_pos _ _ _) lower upper

namespace Development

variable {graph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)
variable (alternative : π ≤ graph.curvature source ∨ graph.curvature (opposite source) ≤ π)
variable (fan_high : π ≤ graph.curvature (opposite source))

include fan_high in
theorem fan_total_le_pi : graph.totalAngleAt (opposite source) ≤ π := by
  unfold curvature at fan_high
  linarith

include alternative fan_high in
/-- The closed first and last patches have no common point other than the fan pole. -/
theorem high_fan_first_last_meet_only_at_zero (x : Plane)
    (first : x ∈ (net.patch 0).hull) (last : x ∈ (net.patch 3).hull) : x = 0 := by
  by_contra nonzero
  have first_span := (net.patch 0).angular_span_bound small_faces alternative (net.patch 0).left x
    (net.patch_left_mem_hull 0) first (by rw [net.patch_pole]; exact net.patch_left_ne_zero 0)
    (by rwa [net.patch_pole])
  have last_span := (net.patch 3).angular_span_bound small_faces alternative x (net.patch 3).right
    last (net.patch_right_mem_hull 3) (by rwa [net.patch_pole])
    (by rw [net.patch_pole]; exact net.patch_right_ne_zero 3)
  rw [net.patch_pole] at first_span last_span
  have end_angle : angle (net.patch 0).left 0 (net.patch 3).right = graph.totalAngleAt (opposite source) := by
    rw [net.patch_left, net.patch_right]
    change angle (graph.openingPoint (opposite source) slit 0) 0
      (graph.openingPoint (opposite source) slit 4) = _
    have difference : graph.openingAngle (opposite source) slit 4 - graph.openingAngle (opposite source) slit 0 =
        graph.totalAngleAt (opposite source) := by rw [graph.openingAngle_last]; change _ - 0 = _; ring
    rw [graph.openingPoint_angle (opposite source) slit 0 4 (by rw [difference]; exact (graph.totalAngleAt_pos _).le)
      (by rw [difference]; exact fan_total_le_pi fan_high), difference]
  have triangle := angle_le_angle_add_angle (0 : Plane) (net.patch 0).left x (net.patch 3).right
  rw [end_angle] at triangle
  linarith

include alternative fan_high in
theorem high_fan_local_pairs : net.LocalPairs := by
  have safe (petal : Bool) : net.Separated (true, 0) (petal, 3) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    have zero := net.high_fan_first_last_meet_only_at_zero alternative fan_high x
      (net.placedTriangle_subset_patch_hull true 0 (interior_subset hx))
      (net.placedTriangle_subset_patch_hull petal 3 (interior_subset hy))
    exact net.zero_not_mem_petal 0 (zero ▸ interior_subset hx)
  refine ⟨safe true, safe false, ?_⟩
  apply Set.disjoint_left.mpr
  intro x hx hy
  have zero := net.high_fan_first_last_meet_only_at_zero alternative fan_high x
    (net.placedTriangle_subset_patch_hull false 0 (interior_subset hy))
    (net.placedTriangle_subset_patch_hull true 3 (interior_subset hx))
  exact net.zero_not_mem_petal 3 (zero ▸ interior_subset hx)

include alternative fan_high in
theorem high_fan_last_cut_clear : Disjoint (net.placedTriangle (true, 1))
    (segment ℝ 0 (graph.openingPoint (opposite source) slit 4)) := by
  apply net.petal_misses_radial_segment alternative 1 (net.patch 1).left _
    (net.patch_left_mem_hull 1) (net.patch_left_ne_zero 1)
  have small_first := ((net.patch 0).corner_angle_bounds small_faces alternative).1
  rw [net.patch_fan_pole_angle] at small_first
  change 2 * (graph.openingAngle (opposite source) slit 1 - 0) < _ at small_first
  have difference : graph.openingAngle (opposite source) slit 4 - graph.openingAngle (opposite source) slit 1 =
      graph.totalAngleAt (opposite source) - graph.openingAngle (opposite source) slit 1 := by rw [graph.openingAngle_last]
  rw [net.patch_left]
  change graph.totalAngleAt (opposite source) ≤ 2 * angle (graph.openingPoint (opposite source) slit 1) 0
    (graph.openingPoint (opposite source) slit 4)
  rw [graph.openingPoint_angle (opposite source) slit 1 4
    (by rw [difference]; linarith [graph.openingAngle_le_total (opposite source) slit 1])
    (by rw [difference]; linarith [fan_total_le_pi fan_high, graph.openingAngle_nonneg (opposite source) slit 1]), difference]
  linarith

include alternative fan_high in
theorem high_fan_first_cut_clear : Disjoint (net.placedTriangle (true, 2))
    (segment ℝ 0 (graph.openingPoint (opposite source) slit 0)) := by
  apply net.petal_misses_radial_segment alternative 2 (net.patch 2).right _
    (net.patch_right_mem_hull 2) (net.patch_right_ne_zero 2)
  have small_last := ((net.patch 3).corner_angle_bounds small_faces alternative).1
  rw [net.patch_fan_pole_angle] at small_last
  change 2 * (graph.openingAngle (opposite source) slit 4 - graph.openingAngle (opposite source) slit 3) < _ at small_last
  rw [graph.openingAngle_last] at small_last
  have difference : graph.openingAngle (opposite source) slit 3 - graph.openingAngle (opposite source) slit 0 =
      graph.openingAngle (opposite source) slit 3 := by change _ - 0 = _; ring
  rw [net.patch_right, angle_comm]
  change graph.totalAngleAt (opposite source) ≤ 2 * angle (graph.openingPoint (opposite source) slit 0) 0
    (graph.openingPoint (opposite source) slit 3)
  rw [graph.openingPoint_angle (opposite source) slit 0 3
    (by rw [difference]; exact graph.openingAngle_nonneg _ _ _)
    (by rw [difference]; exact (graph.openingAngle_le_total _ _ _).trans (fan_total_le_pi fan_high)), difference]
  linarith

include alternative fan_high in
theorem high_fan_finite_cuts_clear : net.FiniteCutsClear :=
  ⟨net.high_fan_last_cut_clear alternative fan_high, net.high_fan_first_cut_clear alternative fan_high⟩

include alternative fan_high in
/-- In this branch, only the two opposite-petal comparisons remain for the whole octahedron. -/
theorem hasEdgeUnfolding_of_high_fan (octahedral : graph.kind = .octahedron)
    (opposite_pairs : net.OppositePetals) : P.HasEdgeUnfolding :=
  net.hasEdgeUnfolding_of_core octahedral (net.high_fan_local_pairs alternative fan_high)
    opposite_pairs (net.high_fan_finite_cuts_clear alternative fan_high)

end Development
end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
