import SixVertexUnfolding.Geometry.OctahedralPocketDiagonal
import SixVertexUnfolding.Geometry.OctahedralPocketHeight
import SixVertexUnfolding.Geometry.OctahedralPocketMiddleFan
import SixVertexUnfolding.Geometry.QuadrilateralRegion
import SixVertexUnfolding.Geometry.PocketContainment

/-! The concrete small-fan pocket lies below the middle base and excludes the middle fan interior. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open Real EuclideanGeometry OctahedralTriangles

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

/-- The four strict vertex bounds extend to the entire two-triangle region. -/
theorem pocket_region_below_base (i : Fin 2) (motion : Plane ≃ᵃⁱ[ℝ] Plane)
    (first : motion (net.patch i.castSucc.succ).left = 0)
    (second : motion (net.patch i.castSucc.succ).right =
      dist (net.patch i.castSucc.succ).left (net.patch i.castSucc.succ).right • direction 0)
    (apex : motion (net.patch i.castSucc.succ).apex =
      dist (net.patch i.castSucc.succ).left (net.patch i.castSucc.succ).apex •
        direction (angle (net.patch i.castSucc.succ).right (net.patch i.castSucc.succ).left (net.patch i.castSucc.succ).apex))
    (small : net.leftFanCorner i + net.rightFanCorner i < π)
    (p : Plane) (left : p ∈ net.placedTriangle (true, i.castSucc.castSucc))
    (right : p ∈ net.placedTriangle (true, i.succ.succ)) :
    quadrilateralRegion (net.patch i.castSucc.castSucc).left p (net.patch i.succ.succ).right 0 ⊆
      {x | (motion x) 1 < 0} := by
  have corners := net.pocket_corners_below_base i motion first second apex small
  have contact := net.opposite_contact_below_base i motion first second apex small p left right
  let height : Plane →ᵃ[ℝ] ℝ :=
    (EuclideanSpace.proj 1).toLinearMap.toAffineMap.comp motion.toAffineEquiv.toAffineMap
  exact quadrilateralRegion_below _ _ _ _ height 0 corners.1 contact corners.2.1 corners.2.2

/-- The middle fan cannot enter the pocket: its interior misses the frontier and its base is outside. -/
theorem middle_fan_disjoint_pocket_region (i : Fin 2)
    (small : net.leftFanCorner i + net.rightFanCorner i < π)
    (p : Plane) (left : p ∈ net.placedTriangle (true, i.castSucc.castSucc))
    (right : p ∈ net.placedTriangle (true, i.succ.succ))
    (diagonal : det ((net.patch i.succ.succ).right - (net.patch i.castSucc.castSucc).left)
        (p - (net.patch i.castSucc.castSucc).left) *
        det ((net.patch i.succ.succ).right - (net.patch i.castSucc.castSucc).left)
          (0 - (net.patch i.castSucc.castSucc).left) < 0 ∨
      det (0 - p) ((net.patch i.castSucc.castSucc).left - p) *
        det (0 - p) ((net.patch i.succ.succ).right - p) < 0) :
    Disjoint (interior (net.placedTriangle (false, i.castSucc.succ)))
      (interior (quadrilateralRegion (net.patch i.castSucc.castSucc).left p (net.patch i.succ.succ).right 0)) := by
  obtain ⟨motion, first, second, apex⟩ := exists_upper_triangle_frame _ _ _
    (net.patch i.castSucc.succ).petal_noncollinear
  have below := net.pocket_region_below_base i motion first second apex small p left right
  have outside : ¬ net.placedTriangle (false, i.castSucc.succ) ⊆
      quadrilateralRegion (net.patch i.castSucc.castSucc).left p (net.patch i.succ.succ).right 0 := by
    intro contained
    have impossible := below (contained (net.patch_left_mem false i.castSucc.succ))
    change (motion (net.patch i.castSucc.succ).left) 1 < 0 at impossible
    rw [first] at impossible
    exact lt_irrefl 0 impossible
  exact (disjoint_interiors_of_boundary_disjoint _ _ (quadrilateralRegion_compact _ _ _ _).isClosed
    (net.placedTriangle_convex _) (net.placedTriangle_interior_nonempty _) outside
    ((net.pocket_boundary_avoids_middle_fan i p left right).mono_right
      (quadrilateralRegion_frontier_subset _ _ _ _ diagonal))).symm

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
