import SixVertexUnfolding.Geometry.NonvertexFacetNeighborhoods

/-! Inside a nondegenerate straight surface segment, no original vertex
occurs and the incident original facets remain exactly the same. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

theorem affine_interval_in_face {P : ConvexPolyhedron} (F : P.Face)
    (curve : ℝ →ᵃ[ℝ] Space) {l r : ℝ} (ordered : l ≤ r)
    (left : curve l ∈ F.val) (right : curve r ∈ F.val) :
    ∀ t ∈ Icc l r, curve t ∈ F.val := by
  intro t ht
  apply F.convex.segment_subset left right
  rw [← image_segment ℝ curve, segment_eq_Icc ordered]
  exact ⟨t, ht, rfl⟩

theorem affine_interior_on_openSegment (curve : ℝ →ᵃ[ℝ] Space) {l r t : ℝ}
    (inside : t ∈ Ioo l r) : curve t ∈ openSegment ℝ (curve l) (curve r) := by
  rw [← image_openSegment ℝ curve, openSegment_eq_Ioo (inside.1.trans inside.2)]
  exact ⟨t, inside, rfl⟩

/-- No interior point of an injectively parametrized solid segment is an original vertex. -/
theorem affine_segment_nonvertex (P : ConvexPolyhedron) (curve : ℝ →ᵃ[ℝ] Space)
    (injective : Function.Injective curve) {l r t : ℝ}
    (left : curve l ∈ P.body) (right : curve r ∈ P.body) (inside : t ∈ Ioo l r) :
    curve t ∉ P.vertices := by
  intro vertex
  have segment := openSegment_subset_segment ℝ (curve l) (curve r) (affine_interior_on_openSegment curve inside)
  rcases P.vertex_in_segment_is_endpoint vertex left right segment with first | last
  · exact inside.1.ne (injective first)
  · exact inside.2.ne' (injective last)

/-- If a supporting facet contains one interior point, it contains the entire segment. -/
theorem facet_contains_affine_interval {P : ConvexPolyhedron} (F : P.Face)
    (curve : ℝ →ᵃ[ℝ] Space) {l r t : ℝ}
    (left : curve l ∈ P.body) (right : curve r ∈ P.body) (inside : t ∈ Ioo l r)
    (member : curve t ∈ F.val) : ∀ s ∈ Icc l r, curve s ∈ F.val := by
  have open_segment := affine_interior_on_openSegment curve inside
  exact affine_interval_in_face F curve (inside.1.trans inside.2).le
    (F.isExposed.isExtreme.left_mem_of_mem_openSegment left right member open_segment)
    (F.isExposed.isExtreme.right_mem_of_mem_openSegment left right member open_segment)

end SixVertexUnfolding.ConvexPolyhedron
