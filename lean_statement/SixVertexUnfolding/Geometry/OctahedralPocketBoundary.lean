import SixVertexUnfolding.Geometry.OctahedralFiniteContact
import SixVertexUnfolding.Geometry.InteriorSegmentAvoidance

/-! Opposite sides of either proposed pocket quadrilateral cannot meet, including at endpoints. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open Real OctahedralTriangles

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

theorem slit_fan_triangles_meet_only_at_zero (x : Plane)
    (first : x ∈ net.placedTriangle (false, 0)) (last : x ∈ net.placedTriangle (false, 3)) : x = 0 := by
  rw [net.fan_placedTriangle] at first last
  exact graph.openingTriangles_meet_only_at_zero small_faces _ _ 0 3 (by decide) x first last

/-- In the last-triple pocket a,p,b,w, neither pair of nonadjacent closed sides intersects. -/
theorem last_pocket_nonadjacent_sides
    (source_order : graph.curvature (opposite source) ≤ graph.curvature source)
    (maximal : ∀ i, graph.curvature (fanNeighbor source i) ≤ graph.curvature (fanNeighbor source slit))
    (p : Plane) (left : p ∈ interior (net.placedTriangle (true, 1)))
    (right : p ∈ interior (net.placedTriangle (true, 3))) :
    Disjoint (segment ℝ (net.patch 1).left p) (segment ℝ 0 (net.patch 3).right) ∧
      Disjoint (segment ℝ p (net.patch 3).right) (segment ℝ 0 (net.patch 1).left) := by
  have cuts := net.selected_finite_cuts_clear source_order maximal
  have local_pairs := net.selected_local_pairs source_order maximal
  have last_cut : Disjoint (net.placedTriangle (true, 1)) (segment ℝ 0 (net.patch 3).right) := by
    simpa only [net.patch_right] using cuts.last
  constructor
  · exact last_cut.mono
      ((net.placedTriangle_convex (true, 1)).segment_subset (net.patch_left_mem true 1) (interior_subset left))
      Set.Subset.rfl
  · have endpoint_outside : (net.patch 3).right ∉ net.placedTriangle (false, 0) := by
      intro member
      exact net.patch_right_ne_zero 3
        (net.slit_fan_triangles_meet_only_at_zero _ member (net.patch_right_mem false 3))
    have avoids := segment_avoids_of_interior_endpoint _ _ (net.placedTriangle_convex (true, 3))
      local_pairs.right.interior_disjoint_closed p (net.patch 3).right right
      (net.patch_right_mem true 3) endpoint_outside
    apply avoids.mono Set.Subset.rfl
    apply (net.placedTriangle_convex (false, 0)).segment_subset (net.fan_pole_mem 0)
    have shared : (net.patch 0).right = (net.patch 1).left := net.consecutive_patch_corner 0
    rw [← shared]
    exact net.patch_right_mem false 0

/-- The reflected first-triple pocket has the same endpoint-safe boundary property. -/
theorem first_pocket_nonadjacent_sides
    (source_order : graph.curvature (opposite source) ≤ graph.curvature source)
    (maximal : ∀ i, graph.curvature (fanNeighbor source i) ≤ graph.curvature (fanNeighbor source slit))
    (p : Plane) (left : p ∈ interior (net.placedTriangle (true, 0)))
    (right : p ∈ interior (net.placedTriangle (true, 2))) :
    Disjoint (segment ℝ p (net.patch 2).right) (segment ℝ 0 (net.patch 0).left) ∧
      Disjoint (segment ℝ (net.patch 0).left p) (segment ℝ 0 (net.patch 2).right) := by
  have cuts := net.selected_finite_cuts_clear source_order maximal
  have local_pairs := net.selected_local_pairs source_order maximal
  have first_cut : Disjoint (net.placedTriangle (true, 2)) (segment ℝ 0 (net.patch 0).left) := by
    simpa only [net.patch_left] using cuts.first
  constructor
  · exact first_cut.mono
      ((net.placedTriangle_convex (true, 2)).segment_subset (interior_subset right) (net.patch_right_mem true 2))
      Set.Subset.rfl
  · have endpoint_outside : (net.patch 0).left ∉ net.placedTriangle (false, 3) := by
      intro member
      exact net.patch_left_ne_zero 0
        (net.slit_fan_triangles_meet_only_at_zero _ (net.patch_left_mem false 0) member)
    have avoids := segment_avoids_of_interior_endpoint _ _ (net.placedTriangle_convex (true, 0))
      local_pairs.left.interior_disjoint_closed p (net.patch 0).left left
      (net.patch_left_mem true 0) endpoint_outside
    rw [segment_symm] at avoids
    apply avoids.mono Set.Subset.rfl
    apply (net.placedTriangle_convex (false, 3)).segment_subset (net.fan_pole_mem 3)
    have shared : (net.patch 2).right = (net.patch 3).left := net.consecutive_patch_corner 2
    rw [shared]
    exact net.patch_left_mem false 3

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
