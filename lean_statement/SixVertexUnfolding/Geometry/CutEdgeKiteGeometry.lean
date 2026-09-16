import SixVertexUnfolding.Geometry.CutStripTriangleTopology
import SixVertexUnfolding.Geometry.BisectorKites

/-! The metric triangles form a kite along each tree edge. Their radial
parametrizations preserve all distances on each individual shortest ray. -/

namespace SixVertexUnfolding.ConvexPolyhedron.CutEdgeMetricModel

open Set

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a}
  {u v : T.vertices} {edge : T.graph.Adj u v} (M : CutEdgeMetricModel T edge)

/-- The paired metric triangles meet exactly on their common base. -/
theorem triangle_intersection :
    convexHull ℝ ({M.left, M.right, M.first} : Set Plane) ∩
      convexHull ℝ ({M.left, M.right, M.second} : Set Plane) = segment ℝ M.left M.right :=
  bisector_kite_intersection _ _ _ _ M.distinct_sources M.base_different M.left_distances M.right_distances

/-- The two source copies lie strictly on opposite sides of the common base. -/
theorem source_sides : det (M.right - M.left) (M.first - M.left) *
    det (M.right - M.left) (M.second - M.left) < 0 :=
  bisector_sites_opposite _ _ _ _ M.distinct_sources M.base_different M.left_distances M.right_distances

/-- Along each individual shortest route, every pair of times has its correct planar distance. -/
theorem radial_distances (routes : C(unitInterval, P.BoundaryCurve))
    (member : ∀ x, routes x ∈ P.geodesicFiber a (T.closedEdgeTarget edge x))
    (x s t : unitInterval) :
    dist (triangleFanMap M.first M.left M.right (x, s))
      (triangleFanMap M.first M.left M.right (x, t)) = P.surfaceDist (routes x s) (routes x t) := by
  have first : routes x 0 = a := congrArg Prod.fst (member x).2
  have last : routes x 1 = T.closedEdgeTarget edge x := congrArg Prod.snd (member x).2
  have geodesic := (member x).1 s t
  rw [first, last] at geodesic
  change dist (AffineMap.lineMap M.first (AffineMap.lineMap M.left M.right (x : ℝ)) (s : ℝ))
    (AffineMap.lineMap M.first (AffineMap.lineMap M.left M.right (x : ℝ)) (t : ℝ)) = _
  rw [dist_lineMap_lineMap, M.first_distances, geodesic]
  change dist (s : ℝ) (t : ℝ) * _ = _ * dist (s : ℝ) (t : ℝ)
  exact mul_comm _ _

end SixVertexUnfolding.ConvexPolyhedron.CutEdgeMetricModel
