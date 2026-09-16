import SixVertexUnfolding.Geometry.OctahedralFanSeeds
import SixVertexUnfolding.Geometry.OuterArcSeed

/-! The protected fan triangle lies in the actual pocket, with its interior seed constructed from the slit gap. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open Real OctahedralTriangles

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

/-- The last-triple pocket contains the entire first fan triangle; its seed is proved, not assumed. -/
theorem first_fan_in_last_pocket
    (source_order : graph.curvature (opposite source) ≤ graph.curvature source)
    (maximal : ∀ i, graph.curvature (fanNeighbor source i) ≤ graph.curvature (fanNeighbor source slit))
    (small : net.leftFanCorner 1 + net.rightFanCorner 1 < π)
    (p : Plane) (left : p ∈ net.placedTriangle (true, 1)) (right : p ∈ net.placedTriangle (true, 3))
    (boundary : QuadrilateralBoundary (net.patch 1).left p (net.patch 3).right 0)
    (diagonal : det ((net.patch 3).right - (net.patch 1).left) (p - (net.patch 1).left) *
        det ((net.patch 3).right - (net.patch 1).left) (0 - (net.patch 1).left) < 0 ∨
      det (0 - p) ((net.patch 1).left - p) * det (0 - p) ((net.patch 3).right - p) < 0) :
    net.placedTriangle (false, 0) ⊆ quadrilateralRegion (net.patch 1).left p (net.patch 3).right 0 := by
  let θ := graph.openingAngle (opposite source) slit
  let R := quadrilateralRegion (net.patch 1).left p (net.patch 3).right 0
  have angles := opening_angles_ordered (graph := graph) (small_faces := small_faces) (source := source) (slit := slit)
  change θ 0 < θ 1 ∧ θ 1 < θ 2 ∧ θ 2 < θ 3 ∧ θ 3 < θ 4 ∧ θ 4 < θ 0 + 2 * π at angles
  obtain ⟨h01, h12, h23, h34, h40⟩ := angles
  obtain ⟨ε_middle, ε_middle_pos, middle_ray⟩ := net.small_midpoint_ray_in_fan 2
  obtain ⟨ε_first, ε_first_pos, first_ray⟩ := net.small_midpoint_ray_in_fan 0
  have middle_safe := net.middle_fan_disjoint_pocket_region 1 small p left right diagonal
  have outside : ∀ r : ℝ, 0 < r → r < ε_middle →
      r • direction ((θ 2 + θ 3) / 2) ∉ interior R := by
    intro r positive short
    exact Set.disjoint_left.mp middle_safe (middle_ray r positive short)
  have far_left : (0 : Plane) ∉ segment ℝ (net.patch 1).left p := fun on_edge =>
    Set.disjoint_left.mp boundary.opposite_left on_edge (left_mem_segment ℝ 0 _)
  have far_right : (0 : Plane) ∉ segment ℝ p (net.patch 3).right := fun on_edge =>
    Set.disjoint_left.mp boundary.opposite_right on_edge (left_mem_segment ℝ 0 _)
  have frontier_eq := quadrilateralRegion_frontier_eq _ _ _ _ diagonal
  obtain ⟨r, r_pos, r_small, seed⟩ := exists_outer_arc_seed R (net.patch 1).left p (net.patch 3).right
    (quadrilateralRegion_compact _ _ _ _).isClosed (quadrilateralRegion_regular _ _ _ _ diagonal)
    _ _ (θ 1) (θ 4) (graph.opening_radius_pos _ _ 1) (graph.opening_radius_pos _ _ 4)
    (by rw [net.patch_left]; rfl) (by rw [net.patch_right]; rfl)
    (by linarith) (by linarith) frontier_eq far_left far_right
    ((θ 2 + θ 3) / 2) ((θ 0 + θ 1) / 2 + 2 * π)
    ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
    ε_middle ε_middle_pos outside ε_first ε_first_pos
  rw [direction_add_two_pi] at seed
  exact net.first_patch_in_pocket_region_of_seed source_order maximal p left right frontier_eq.subset
    false (r • direction ((θ 0 + θ 1) / 2)) (first_ray r r_pos r_small) seed

/-- The reflected first-triple pocket contains the entire last fan triangle. -/
theorem last_fan_in_first_pocket
    (source_order : graph.curvature (opposite source) ≤ graph.curvature source)
    (maximal : ∀ i, graph.curvature (fanNeighbor source i) ≤ graph.curvature (fanNeighbor source slit))
    (small : net.leftFanCorner 0 + net.rightFanCorner 0 < π)
    (p : Plane) (left : p ∈ net.placedTriangle (true, 0)) (right : p ∈ net.placedTriangle (true, 2))
    (boundary : QuadrilateralBoundary (net.patch 0).left p (net.patch 2).right 0)
    (diagonal : det ((net.patch 2).right - (net.patch 0).left) (p - (net.patch 0).left) *
        det ((net.patch 2).right - (net.patch 0).left) (0 - (net.patch 0).left) < 0 ∨
      det (0 - p) ((net.patch 0).left - p) * det (0 - p) ((net.patch 2).right - p) < 0) :
    net.placedTriangle (false, 3) ⊆ quadrilateralRegion (net.patch 0).left p (net.patch 2).right 0 := by
  let θ := graph.openingAngle (opposite source) slit
  let R := quadrilateralRegion (net.patch 0).left p (net.patch 2).right 0
  have angles := opening_angles_ordered (graph := graph) (small_faces := small_faces) (source := source) (slit := slit)
  change θ 0 < θ 1 ∧ θ 1 < θ 2 ∧ θ 2 < θ 3 ∧ θ 3 < θ 4 ∧ θ 4 < θ 0 + 2 * π at angles
  obtain ⟨h01, h12, h23, h34, h40⟩ := angles
  obtain ⟨ε_middle, ε_middle_pos, middle_ray⟩ := net.small_midpoint_ray_in_fan 1
  obtain ⟨ε_last, ε_last_pos, last_ray⟩ := net.small_midpoint_ray_in_fan 3
  have middle_safe := net.middle_fan_disjoint_pocket_region 0 small p left right diagonal
  have outside : ∀ r : ℝ, 0 < r → r < ε_middle →
      r • direction ((θ 1 + θ 2) / 2) ∉ interior R := by
    intro r positive short
    exact Set.disjoint_left.mp middle_safe (middle_ray r positive short)
  have far_left : (0 : Plane) ∉ segment ℝ (net.patch 0).left p := fun on_edge =>
    Set.disjoint_left.mp boundary.opposite_left on_edge (left_mem_segment ℝ 0 _)
  have far_right : (0 : Plane) ∉ segment ℝ p (net.patch 2).right := fun on_edge =>
    Set.disjoint_left.mp boundary.opposite_right on_edge (left_mem_segment ℝ 0 _)
  have frontier_eq := quadrilateralRegion_frontier_eq _ _ _ _ diagonal
  obtain ⟨r, r_pos, r_small, seed⟩ := exists_outer_arc_seed R (net.patch 0).left p (net.patch 2).right
    (quadrilateralRegion_compact _ _ _ _).isClosed (quadrilateralRegion_regular _ _ _ _ diagonal)
    _ _ (θ 0) (θ 3) (graph.opening_radius_pos _ _ 0) (graph.opening_radius_pos _ _ 3)
    (by rw [net.patch_left]; rfl) (by rw [net.patch_right]; rfl)
    (by linarith) (by linarith) frontier_eq far_left far_right
    ((θ 1 + θ 2) / 2) ((θ 3 + θ 4) / 2)
    ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
    ε_middle ε_middle_pos outside ε_last ε_last_pos
  exact net.last_patch_in_pocket_region_of_seed source_order maximal p left right frontier_eq.subset
    false (r • direction ((θ 3 + θ 4) / 2)) (last_ray r r_pos r_small) seed

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
