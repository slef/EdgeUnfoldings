import SixVertexUnfolding.Geometry.OctahedralPocketFan
import SixVertexUnfolding.Geometry.CornerSeed

/-! The protected slit corner misses every side of the pocket boundary. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open Real EuclideanGeometry OctahedralTriangles

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

/-- The first slit corner is off the last-triple boundary, including all segment endpoints. -/
theorem first_slit_corner_off_last_pocket
    (source_order : graph.curvature (opposite source) ≤ graph.curvature source)
    (maximal : ∀ i, graph.curvature (fanNeighbor source i) ≤ graph.curvature (fanNeighbor source slit))
    (p : Plane) (left : p ∈ interior (net.placedTriangle (true, 1)))
    (right : p ∈ interior (net.placedTriangle (true, 3))) :
    (net.patch 0).left ∉ segment ℝ (net.patch 1).left p ∪ segment ℝ p (net.patch 3).right ∪
      segment ℝ 0 (net.patch 3).right ∪ segment ℝ 0 (net.patch 1).left := by
  have local_pairs := net.selected_local_pairs source_order maximal
  have in_fan := net.patch_left_mem false 0
  have shared : (net.patch 0).right = (net.patch 1).left := net.consecutive_patch_corner 0
  have different_left : (net.patch 0).left ≠ (net.patch 1).left := by
    rw [← shared]
    exact ne₁₂_of_not_collinear (net.patch 0).fan_noncollinear
  have different_right : (net.patch 0).left ≠ (net.patch 3).right := by
    intro same
    apply net.patch_left_ne_zero 0
    exact net.slit_fan_triangles_meet_only_at_zero _ in_fan (same ▸ net.patch_right_mem false 3)
  have misses_left := point_avoids_segment_to_interior _ _ (net.placedTriangle_convex (true, 1))
    (net.neighboring_fan_petal 0).symm.interior_disjoint_closed _ p _
    (net.patch_left_mem true 1) left in_fan different_left
  have misses_right := point_avoids_segment_to_interior _ _ (net.placedTriangle_convex (true, 3))
    local_pairs.right.interior_disjoint_closed _ p _ (net.patch_right_mem true 3) right in_fan different_right
  rintro (((on_left | on_right) | on_last_ray) | on_first_ray)
  · exact misses_left on_left
  · exact misses_right (by rwa [segment_symm ℝ (net.patch 3).right p])
  · apply net.patch_left_ne_zero 0
    exact net.slit_fan_triangles_meet_only_at_zero _ in_fan
      ((net.placedTriangle_convex (false, 3)).segment_subset (net.fan_pole_mem 3) (net.patch_right_mem false 3) on_last_ray)
  · rw [← shared] at on_first_ray
    have collinear := (mem_segment_iff_wbtw.mp on_first_ray).collinear
    apply (net.patch 0).fan_noncollinear
    rw [net.patch_pole]
    convert collinear using 1
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto

/-- The last slit corner is off the reflected first-triple boundary. -/
theorem last_slit_corner_off_first_pocket
    (source_order : graph.curvature (opposite source) ≤ graph.curvature source)
    (maximal : ∀ i, graph.curvature (fanNeighbor source i) ≤ graph.curvature (fanNeighbor source slit))
    (p : Plane) (left : p ∈ interior (net.placedTriangle (true, 0)))
    (right : p ∈ interior (net.placedTriangle (true, 2))) :
    (net.patch 3).right ∉ segment ℝ (net.patch 0).left p ∪ segment ℝ p (net.patch 2).right ∪
      segment ℝ 0 (net.patch 2).right ∪ segment ℝ 0 (net.patch 0).left := by
  have local_pairs := net.selected_local_pairs source_order maximal
  have in_fan := net.patch_right_mem false 3
  have shared : (net.patch 2).right = (net.patch 3).left := net.consecutive_patch_corner 2
  have different_left : (net.patch 3).right ≠ (net.patch 0).left := by
    intro same
    apply net.patch_right_ne_zero 3
    exact net.slit_fan_triangles_meet_only_at_zero _ (same ▸ net.patch_left_mem false 0) in_fan
  have different_right : (net.patch 3).right ≠ (net.patch 2).right := by
    rw [shared]
    exact (ne₁₂_of_not_collinear (net.patch 3).fan_noncollinear).symm
  have misses_left := point_avoids_segment_to_interior _ _ (net.placedTriangle_convex (true, 0))
    local_pairs.left.interior_disjoint_closed _ p _ (net.patch_left_mem true 0) left in_fan different_left
  have misses_right := point_avoids_segment_to_interior _ _ (net.placedTriangle_convex (true, 2))
    (net.neighboring_petal_fan 2).interior_disjoint_closed _ p _
    (net.patch_right_mem true 2) right in_fan different_right
  rintro (((on_left | on_right) | on_last_ray) | on_first_ray)
  · exact misses_left on_left
  · exact misses_right (by rwa [segment_symm ℝ (net.patch 2).right p])
  · rw [shared] at on_last_ray
    have collinear := (mem_segment_iff_wbtw.mp on_last_ray).collinear
    apply (net.patch 3).fan_noncollinear
    rw [net.patch_pole]
    convert collinear using 1
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  · apply net.patch_right_ne_zero 3
    exact net.slit_fan_triangles_meet_only_at_zero _
      ((net.placedTriangle_convex (false, 0)).segment_subset (net.fan_pole_mem 0) (net.patch_left_mem false 0) on_first_ray) in_fan

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
