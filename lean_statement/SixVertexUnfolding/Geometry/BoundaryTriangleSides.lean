import SixVertexUnfolding.Geometry.JoinedTriangleInterior

/-! Two triangles contained in a region cannot lie across a segment of the region's frontier. -/

namespace SixVertexUnfolding

/-- Opposite sides would make the open common base interior to the region, contradicting the frontier. -/
theorem triangles_on_frontier_same_side (region : Set Plane) (a b c d : Plane)
    (edge : segment ℝ a b ⊆ frontier region)
    (first : convexHull ℝ ({a, b, c} : Set Plane) ⊆ region)
    (second : convexHull ℝ ({a, b, d} : Set Plane) ⊆ region) :
    0 ≤ det (b - a) (c - a) * det (b - a) (d - a) := by
  by_contra negative
  have opposite := lt_of_not_ge negative
  let center := (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b
  have on_open : center ∈ openSegment ℝ a b := ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
  have on_boundary := edge (openSegment_subset_segment ℝ a b on_open)
  exact on_boundary.2 (interior_mono (Set.union_subset first second)
    (open_base_in_joined_triangles_of_opposite a b c d opposite on_open))

end SixVertexUnfolding
