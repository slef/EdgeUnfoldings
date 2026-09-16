import SixVertexUnfolding.Geometry.QuadrilateralRegionTopology
import SixVertexUnfolding.Geometry.JoinedTriangleBoundary
import SixVertexUnfolding.Geometry.ClosedRegionComponent

/-! The four-sided trace is exactly the boundary of the concrete pocket region. -/

namespace SixVertexUnfolding

/-- The region has precisely the four named boundary segments in either diagonal branch. -/
theorem quadrilateralRegion_frontier_eq (a p b w : Plane)
    (diagonal : det (b - a) (p - a) * det (b - a) (w - a) < 0 ∨
      det (w - p) (a - p) * det (w - p) (b - p) < 0) :
    frontier (quadrilateralRegion a p b w) =
      segment ℝ a p ∪ segment ℝ p b ∪ segment ℝ w b ∪ segment ℝ w a := by
  unfold quadrilateralRegion
  split_ifs with first
  · simpa only [segment_symm ℝ b p, segment_symm ℝ a w, segment_symm ℝ b w,
      Set.union_assoc, Set.union_comm, Set.union_left_comm] using joined_triangles_frontier_eq a b p w first
  · simpa only [segment_symm ℝ p a, Set.union_assoc, Set.union_comm, Set.union_left_comm] using
      joined_triangles_frontier_eq p w a b (diagonal.resolve_left first)

/-- Any seed inside the region selects exactly its interior in the four-side complement. -/
theorem quadrilateralRegion_interior_component (a p b w : Plane)
    (diagonal : det (b - a) (p - a) * det (b - a) (w - a) < 0 ∨
      det (w - p) (a - p) * det (w - p) (b - p) < 0)
    (seed : Plane) (inside : seed ∈ interior (quadrilateralRegion a p b w)) :
    connectedComponentIn (segment ℝ a p ∪ segment ℝ p b ∪ segment ℝ w b ∪ segment ℝ w a)ᶜ seed =
      interior (quadrilateralRegion a p b w) := by
  rw [← quadrilateralRegion_frontier_eq a p b w diagonal]
  exact closed_region_interior_component _ (quadrilateralRegion_compact _ _ _ _).isClosed
    (quadrilateralRegion_interior_pathConnected a p b w diagonal).isConnected.isPreconnected seed inside

/-- Its closed component is exactly the two-triangle region, including every boundary point. -/
theorem quadrilateralRegion_closure_component (a p b w : Plane)
    (diagonal : det (b - a) (p - a) * det (b - a) (w - a) < 0 ∨
      det (w - p) (a - p) * det (w - p) (b - p) < 0)
    (seed : Plane) (inside : seed ∈ interior (quadrilateralRegion a p b w)) :
    closure (connectedComponentIn (segment ℝ a p ∪ segment ℝ p b ∪ segment ℝ w b ∪ segment ℝ w a)ᶜ seed) =
      quadrilateralRegion a p b w := by
  rw [quadrilateralRegion_interior_component a p b w diagonal seed inside]
  exact quadrilateralRegion_regular a p b w diagonal

end SixVertexUnfolding
