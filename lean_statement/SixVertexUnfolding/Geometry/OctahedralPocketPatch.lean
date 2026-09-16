import SixVertexUnfolding.Geometry.OctahedralPocketCorner

/-! Both whole triangles of the protected slit-adjacent patch lie in the pocket. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open Real OctahedralTriangles

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

/-- The first patch is wholly contained in the last-triple pocket, with its slit corner strictly inside. -/
theorem first_patch_in_last_pocket
    (source_order : graph.curvature (opposite source) ≤ graph.curvature source)
    (maximal : ∀ i, graph.curvature (fanNeighbor source i) ≤ graph.curvature (fanNeighbor source slit))
    (small : net.leftFanCorner 1 + net.rightFanCorner 1 < π)
    (p : Plane) (left : p ∈ interior (net.placedTriangle (true, 1)))
    (right : p ∈ interior (net.placedTriangle (true, 3)))
    (boundary : QuadrilateralBoundary (net.patch 1).left p (net.patch 3).right 0)
    (diagonal : det ((net.patch 3).right - (net.patch 1).left) (p - (net.patch 1).left) *
        det ((net.patch 3).right - (net.patch 1).left) (0 - (net.patch 1).left) < 0 ∨
      det (0 - p) ((net.patch 1).left - p) * det (0 - p) ((net.patch 3).right - p) < 0) :
    (net.patch 0).left ∈ interior (quadrilateralRegion (net.patch 1).left p (net.patch 3).right 0) ∧
      ∀ petal : Bool, net.placedTriangle (petal, 0) ⊆ quadrilateralRegion (net.patch 1).left p (net.patch 3).right 0 := by
  have fan := net.first_fan_in_last_pocket source_order maximal small p (interior_subset left) (interior_subset right) boundary diagonal
  have frontier := quadrilateralRegion_frontier_subset _ _ _ _ diagonal
  have corner_inside : (net.patch 0).left ∈ interior (quadrilateralRegion (net.patch 1).left p (net.patch 3).right 0) := by
    by_contra outside
    have on_boundary := (mem_frontier_iff_notMem_interior (fan (net.patch_left_mem false 0))).mpr outside
    exact net.first_slit_corner_off_last_pocket source_order maximal p left right (frontier on_boundary)
  refine ⟨corner_inside, fun petal => ?_⟩
  cases petal
  · exact fan
  · exact convex_face_in_region_of_corner _ _ (quadrilateralRegion_compact _ _ _ _).isClosed
      (net.placedTriangle_convex _) (net.placedTriangle_regular _)
      ((net.last_pocket_boundary_avoids_first_patch source_order maximal p (interior_subset left) (interior_subset right) true).mono_right frontier)
      (net.patch 0).left (net.patch_left_mem true 0) corner_inside

/-- The last patch is wholly contained in the reflected first-triple pocket. -/
theorem last_patch_in_first_pocket
    (source_order : graph.curvature (opposite source) ≤ graph.curvature source)
    (maximal : ∀ i, graph.curvature (fanNeighbor source i) ≤ graph.curvature (fanNeighbor source slit))
    (small : net.leftFanCorner 0 + net.rightFanCorner 0 < π)
    (p : Plane) (left : p ∈ interior (net.placedTriangle (true, 0)))
    (right : p ∈ interior (net.placedTriangle (true, 2)))
    (boundary : QuadrilateralBoundary (net.patch 0).left p (net.patch 2).right 0)
    (diagonal : det ((net.patch 2).right - (net.patch 0).left) (p - (net.patch 0).left) *
        det ((net.patch 2).right - (net.patch 0).left) (0 - (net.patch 0).left) < 0 ∨
      det (0 - p) ((net.patch 0).left - p) * det (0 - p) ((net.patch 2).right - p) < 0) :
    (net.patch 3).right ∈ interior (quadrilateralRegion (net.patch 0).left p (net.patch 2).right 0) ∧
      ∀ petal : Bool, net.placedTriangle (petal, 3) ⊆ quadrilateralRegion (net.patch 0).left p (net.patch 2).right 0 := by
  have fan := net.last_fan_in_first_pocket source_order maximal small p (interior_subset left) (interior_subset right) boundary diagonal
  have frontier := quadrilateralRegion_frontier_subset _ _ _ _ diagonal
  have corner_inside : (net.patch 3).right ∈ interior (quadrilateralRegion (net.patch 0).left p (net.patch 2).right 0) := by
    by_contra outside
    have on_boundary := (mem_frontier_iff_notMem_interior (fan (net.patch_right_mem false 3))).mpr outside
    exact net.last_slit_corner_off_first_pocket source_order maximal p left right (frontier on_boundary)
  refine ⟨corner_inside, fun petal => ?_⟩
  cases petal
  · exact fan
  · exact convex_face_in_region_of_corner _ _ (quadrilateralRegion_compact _ _ _ _).isClosed
      (net.placedTriangle_convex _) (net.placedTriangle_regular _)
      ((net.first_pocket_boundary_avoids_last_patch source_order maximal p (interior_subset left) (interior_subset right) true).mono_right frontier)
      (net.patch 3).right (net.patch_right_mem true 3) corner_inside

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
