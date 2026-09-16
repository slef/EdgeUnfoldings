import SixVertexUnfolding.Geometry.TriangleBoundary
import SixVertexUnfolding.Geometry.PlacedFaces

/-! Closedness, boundary edges, and convex-hull descriptions for placed original triangles. -/

namespace SixVertexUnfolding.ConvexPolyhedron.Face

variable {P : ConvexPolyhedron} (F : P.Face)

/-- An affine image of an original facet is compact, hence closed. -/
theorem placed_face_closed (place : Space →ᵃ[ℝ] Plane) : IsClosed (place '' F.val) :=
  (F.isCompact.image place.continuous_of_finiteDimensional).isClosed

/-- A rigidly placed whole facet is the closure of its ordinary planar interior. -/
theorem placed_face_regular (place : Space →ᵃ[ℝ] Plane)
    (rigid : ∀ x ∈ F.val, ∀ y ∈ F.val, dist (place x) (place y) = dist x y) :
    closure (interior (place '' F.val)) = place '' F.val := by
  rw [(F.convex.affine_image place).closure_interior_eq_closure_of_nonempty_interior
    (F.placed_face_interior_nonempty place rigid), (F.placed_face_closed place).closure_eq]

/-- A placed triangular facet is exactly the convex hull of its three placed vertices. -/
theorem placed_triangle_hull (place : Space →ᵃ[ℝ] Plane) (a b c : Space)
    (vertices : F.val ∩ (P.vertices : Set Space) = {a, b, c}) :
    place '' F.val = convexHull ℝ ({place a, place b, place c} : Set Plane) := by
  rw [F.eq_convexHull_vertices, vertices, place.image_convexHull,
    Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]

/-- The placed facet's boundary is covered by its three placed original edges. -/
theorem placed_triangle_frontier (place : Space →ᵃ[ℝ] Plane) (a b c : Space)
    (vertices : F.val ∩ (P.vertices : Set Space) = {a, b, c})
    (noncollinear : ¬ Collinear ℝ ({place a, place b, place c} : Set Plane)) :
    frontier (place '' F.val) ⊆ segment ℝ (place a) (place b) ∪
      (segment ℝ (place a) (place c) ∪ segment ℝ (place b) (place c)) := by
  rw [F.placed_triangle_hull place a b c vertices]
  exact triangle_frontier_subset_edges _ _ _ noncollinear

end SixVertexUnfolding.ConvexPolyhedron.Face
