import SixVertexUnfolding.Geometry.OctahedralPocketRegion
import SixVertexUnfolding.Geometry.QuadrilateralRegionBoundary

/-! Hypothetical overlap supplies the concrete region; patch containment is reduced to interior seeds. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open Real OctahedralTriangles

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

/-- In either orientation, small-fan overlap produces a nonempty bounded region avoiding the middle fan.
The diagonal and boundary certificates are derived from the actual development. -/
theorem exists_small_fan_pocket_region (i : Fin 2)
    (source_order : graph.curvature (opposite source) ≤ graph.curvature source)
    (maximal : ∀ j, graph.curvature (fanNeighbor source j) ≤ graph.curvature (fanNeighbor source slit))
    (small : net.leftFanCorner i + net.rightFanCorner i < π)
    (overlap : ¬ net.Separated (true, i.castSucc.castSucc) (true, i.succ.succ)) :
    ∃ p, p ∈ interior (net.placedTriangle (true, i.castSucc.castSucc)) ∧
      p ∈ interior (net.placedTriangle (true, i.succ.succ)) ∧
      IsPathConnected (interior (quadrilateralRegion (net.patch i.castSucc.castSucc).left p (net.patch i.succ.succ).right 0)) ∧
      frontier (quadrilateralRegion (net.patch i.castSucc.castSucc).left p (net.patch i.succ.succ).right 0) =
        segment ℝ (net.patch i.castSucc.castSucc).left p ∪ segment ℝ p (net.patch i.succ.succ).right ∪
          segment ℝ 0 (net.patch i.succ.succ).right ∪ segment ℝ 0 (net.patch i.castSucc.castSucc).left ∧
      Disjoint (interior (net.placedTriangle (false, i.castSucc.succ)))
        (interior (quadrilateralRegion (net.patch i.castSucc.castSucc).left p (net.patch i.succ.succ).right 0)) := by
  fin_cases i
  · obtain ⟨p, left, right, _, diagonal⟩ := net.exists_first_pocket_diagonal source_order maximal overlap
    exact ⟨p, left, right, quadrilateralRegion_interior_pathConnected _ _ _ _ diagonal,
      quadrilateralRegion_frontier_eq _ _ _ _ diagonal,
      net.middle_fan_disjoint_pocket_region 0 small p (interior_subset left) (interior_subset right) diagonal⟩
  · obtain ⟨p, left, right, _, diagonal⟩ := net.exists_last_pocket_diagonal source_order maximal overlap
    exact ⟨p, left, right, quadrilateralRegion_interior_pathConnected _ _ _ _ diagonal,
      quadrilateralRegion_frontier_eq _ _ _ _ diagonal,
      net.middle_fan_disjoint_pocket_region 1 small p (interior_subset left) (interior_subset right) diagonal⟩

/-- A seed in the last-triple region suffices for either whole triangle of the first patch. -/
theorem first_patch_in_pocket_region_of_seed
    (source_order : graph.curvature (opposite source) ≤ graph.curvature source)
    (maximal : ∀ i, graph.curvature (fanNeighbor source i) ≤ graph.curvature (fanNeighbor source slit))
    (p : Plane) (left : p ∈ net.placedTriangle (true, 1)) (right : p ∈ net.placedTriangle (true, 3))
    (boundary : frontier (quadrilateralRegion (net.patch 1).left p (net.patch 3).right 0) ⊆
      segment ℝ (net.patch 1).left p ∪ segment ℝ p (net.patch 3).right ∪
        segment ℝ 0 (net.patch 3).right ∪ segment ℝ 0 (net.patch 1).left)
    (petal : Bool) (seed : Plane) (in_patch : seed ∈ interior (net.placedTriangle (petal, 0)))
    (in_region : seed ∈ interior (quadrilateralRegion (net.patch 1).left p (net.patch 3).right 0)) :
    net.placedTriangle (petal, 0) ⊆ quadrilateralRegion (net.patch 1).left p (net.patch 3).right 0 :=
  convex_face_in_closed_region _ _ (quadrilateralRegion_compact _ _ _ _).isClosed
    (net.placedTriangle_convex _) (net.placedTriangle_regular _)
    ((net.last_pocket_boundary_avoids_first_patch source_order maximal p left right petal).mono_right boundary)
    seed in_patch in_region

/-- The reflected first-triple region has the same seed-to-whole-patch implication. -/
theorem last_patch_in_pocket_region_of_seed
    (source_order : graph.curvature (opposite source) ≤ graph.curvature source)
    (maximal : ∀ i, graph.curvature (fanNeighbor source i) ≤ graph.curvature (fanNeighbor source slit))
    (p : Plane) (left : p ∈ net.placedTriangle (true, 0)) (right : p ∈ net.placedTriangle (true, 2))
    (boundary : frontier (quadrilateralRegion (net.patch 0).left p (net.patch 2).right 0) ⊆
      segment ℝ (net.patch 0).left p ∪ segment ℝ p (net.patch 2).right ∪
        segment ℝ 0 (net.patch 2).right ∪ segment ℝ 0 (net.patch 0).left)
    (petal : Bool) (seed : Plane) (in_patch : seed ∈ interior (net.placedTriangle (petal, 3)))
    (in_region : seed ∈ interior (quadrilateralRegion (net.patch 0).left p (net.patch 2).right 0)) :
    net.placedTriangle (petal, 3) ⊆ quadrilateralRegion (net.patch 0).left p (net.patch 2).right 0 :=
  convex_face_in_closed_region _ _ (quadrilateralRegion_compact _ _ _ _).isClosed
    (net.placedTriangle_convex _) (net.placedTriangle_regular _)
    ((net.first_pocket_boundary_avoids_last_patch source_order maximal p left right petal).mono_right boundary)
    seed in_patch in_region

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
