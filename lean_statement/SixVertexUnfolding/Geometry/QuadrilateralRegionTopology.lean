import SixVertexUnfolding.Geometry.QuadrilateralRegion
import SixVertexUnfolding.Geometry.JoinedTriangleTopology

/-! The concrete pocket has one connected interior and no extra boundary pieces. -/

namespace SixVertexUnfolding

/-- The candidate pocket has a path-connected interior, even when a corner is reflex or straight. -/
theorem quadrilateralRegion_interior_pathConnected (a p b w : Plane)
    (diagonal : det (b - a) (p - a) * det (b - a) (w - a) < 0 ∨
      det (w - p) (a - p) * det (w - p) (b - p) < 0) :
    IsPathConnected (interior (quadrilateralRegion a p b w)) := by
  unfold quadrilateralRegion
  split_ifs with first
  · exact joined_triangles_interior_pathConnected a b p w first
  · exact joined_triangles_interior_pathConnected p w a b (diagonal.resolve_left first)

/-- The whole closed pocket is exactly the closure of its interior. -/
theorem quadrilateralRegion_regular (a p b w : Plane)
    (diagonal : det (b - a) (p - a) * det (b - a) (w - a) < 0 ∨
      det (w - p) (a - p) * det (w - p) (b - p) < 0) :
    closure (interior (quadrilateralRegion a p b w)) = quadrilateralRegion a p b w := by
  unfold quadrilateralRegion
  split_ifs with first
  · exact joined_triangles_regular a b p w first
  · exact joined_triangles_regular p w a b (diagonal.resolve_left first)

end SixVertexUnfolding
