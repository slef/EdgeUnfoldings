import SixVertexUnfolding.Geometry.TriangleTopology

/-! A segment from an interior point to an allowed boundary endpoint cannot touch a separated closed set. -/

namespace SixVertexUnfolding

/-- Boundary tangencies cause no problem when the only possible boundary endpoint is excluded. -/
theorem segment_avoids_of_interior_endpoint (s t : Set Plane) (convex : Convex ℝ s)
    (safe : Disjoint (interior s) t) (p b : Plane)
    (inside : p ∈ interior s) (endpoint : b ∈ s) (outside : b ∉ t) :
    Disjoint (segment ℝ p b) t := by
  apply Set.disjoint_left.mpr
  intro x on_segment in_other
  rw [← insert_endpoints_openSegment] at on_segment
  rcases on_segment with rfl | rfl | between
  · exact Set.disjoint_left.mp safe inside in_other
  · exact outside in_other
  · exact Set.disjoint_left.mp safe
      (convex.openSegment_interior_self_subset_interior inside endpoint between) in_other

end SixVertexUnfolding
