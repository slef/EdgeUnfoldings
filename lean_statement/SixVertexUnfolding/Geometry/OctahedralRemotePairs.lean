import SixVertexUnfolding.Geometry.OctahedralFanBoundary
import SixVertexUnfolding.Geometry.BoundaryExclusion

/-! The four remote pairs follow from protected target edges; the development is never changed. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open OctahedralTriangles

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

/-- Protecting the three target edges suffices: the petal already has a corner outside that target. -/
theorem remote_of_protected_edges (i : Fin 4)
    (left : Disjoint (interior (net.placedTriangle (true, i)))
      (segment ℝ 0 (graph.openingPoint (opposite source) slit (i + 2).castSucc)))
    (right : Disjoint (interior (net.placedTriangle (true, i)))
      (segment ℝ 0 (graph.openingPoint (opposite source) slit (i + 2).succ)))
    (opposite : net.Separated (true, i) (true, i + 2)) : net.Separated (true, i) (false, i + 2) := by
  apply Disjoint.symm
  apply disjoint_interiors_of_boundary_disjoint _ _ (net.placedTriangle_closed _)
    (net.placedTriangle_convex _) (net.placedTriangle_interior_nonempty _)
    (net.petal_not_subset_opposite_fan i)
  apply Set.disjoint_left.mpr
  intro x inside boundary
  rcases net.fan_frontier_covered (i + 2) boundary with first | second | base
  · exact Set.disjoint_left.mp left inside first
  · exact Set.disjoint_left.mp right inside second
  · exact Set.disjoint_left.mp opposite.interior_disjoint_closed inside base

/-- The first remote pair has no finite-cut edge on its target boundary. -/
theorem remote_zero (local_pair : net.Separated (true, 0) (false, 3))
    (opposite_pair : net.Separated (true, 0) (true, 2)) : net.Separated (true, 0) (false, 2) := by
  apply net.remote_of_protected_edges 0 _ _ opposite_pair
  · exact Disjoint.mono_right (net.radial_edge_in_previous_fan 1)
      (net.neighboring_petal_fan 0).interior_disjoint_closed
  · exact Disjoint.mono_right (net.radial_edge_in_next_fan 2) local_pair.interior_disjoint_closed

/-- The second remote pair uses the last finite slit segment and two already protected neighboring faces. -/
theorem remote_one
    (cut_clear : Disjoint (net.placedTriangle (true, 1))
      (segment ℝ 0 (graph.openingPoint (opposite source) slit 4)))
    (opposite_pair : net.Separated (true, 1) (true, 3)) : net.Separated (true, 1) (false, 3) := by
  apply net.remote_of_protected_edges 1 _ _ opposite_pair
  · exact Disjoint.mono_right (net.radial_edge_in_previous_fan 2)
      (net.neighboring_petal_fan 1).interior_disjoint_closed
  · exact Disjoint.mono_left interior_subset cut_clear

/-- Reflection of the preceding boundary argument, stated directly in the same net. -/
theorem remote_two
    (cut_clear : Disjoint (net.placedTriangle (true, 2))
      (segment ℝ 0 (graph.openingPoint (opposite source) slit 0)))
    (opposite_pair : net.Separated (true, 0) (true, 2)) : net.Separated (true, 2) (false, 0) := by
  apply net.remote_of_protected_edges 2 _ _ opposite_pair.symm
  · exact Disjoint.mono_left interior_subset cut_clear
  · exact Disjoint.mono_right (net.radial_edge_in_next_fan 0)
      (net.neighboring_fan_petal 1).symm.interior_disjoint_closed

/-- The last remote pair also has all three target edges covered by already separated faces. -/
theorem remote_three (local_pair : net.Separated (true, 3) (false, 0))
    (opposite_pair : net.Separated (true, 1) (true, 3)) : net.Separated (true, 3) (false, 1) := by
  apply net.remote_of_protected_edges 3 _ _ opposite_pair.symm
  · exact Disjoint.mono_right (net.radial_edge_in_previous_fan 0) local_pair.interior_disjoint_closed
  · exact Disjoint.mono_right (net.radial_edge_in_next_fan 1)
      (net.neighboring_fan_petal 2).symm.interior_disjoint_closed

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
