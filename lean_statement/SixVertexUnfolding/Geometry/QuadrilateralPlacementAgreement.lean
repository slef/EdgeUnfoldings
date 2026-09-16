import SixVertexUnfolding.Geometry.CrossingHingeSides
import SixVertexUnfolding.Geometry.HingeSideOrder
import SixVertexUnfolding.Geometry.FacetCoordinates
import SixVertexUnfolding.Geometry.TriangleNondegeneracy

/-! Outward unfolding across a flat quadrilateral diagonal preserves a single rigid whole-face placement. -/

namespace SixVertexUnfolding.ConvexPolyhedron.Face

variable {P : ConvexPolyhedron} (F : P.Face)

/-- Two rigid placements agreeing along a crossing diagonal agree on the whole facet. -/
theorem placements_agree_across_diagonal (a b c d : P.Vertex)
    (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c) (ad : a ≠ d) (bd : b ≠ d)
    (aF : (a : Space) ∈ F.val) (bF : (b : Space) ∈ F.val)
    (cF : (c : Space) ∈ F.val) (dF : (d : Space) ∈ F.val)
    (crossing : ∃ q : Space, q ∈ segment ℝ (a : Space) b ∧ q ∈ openSegment ℝ (c : Space) d)
    (left right : Space →ᵃ[ℝ] Plane)
    (left_rigid : ∀ x ∈ F.val, ∀ y ∈ F.val, dist (left x) (left y) = dist x y)
    (right_rigid : ∀ x ∈ F.val, ∀ y ∈ F.val, dist (right x) (right y) = dist x y)
    (at_a : left a = right a) (at_b : left b = right b)
    (outward : OppositeHingeSides (left a) (left b) (left c) (right d)) :
    Set.EqOn left right F.val := by
  have noncollinear := P.placed_triangle_noncollinear a b c ab ac bc (left a) (left b) (left c)
    (left_rigid a aF b bF) (left_rigid a aF c cF) (left_rigid b bF c cF)
  obtain ⟨q, on_hinge, across⟩ := crossing
  have placed_hinge : left q ∈ segment ℝ (left a) (left b) := by
    rw [← image_segment ℝ left]
    exact ⟨q, on_hinge, rfl⟩
  have placed_crossing : left q ∈ openSegment ℝ (left c) (left d) := by
    rw [← image_openSegment ℝ left]
    exact ⟨q, across, rfl⟩
  have left_outward := oppositeHingeSides_of_crossing _ _ _ _ _
    (ne₁₂_of_not_collinear noncollinear) placed_hinge placed_crossing
  have at_d : left d = right d := by
    apply outward_point_unique (left a) (left b) (left c) _ _ noncollinear
    · rw [left_rigid a aF d dF, at_a, right_rigid a aF d dF]
    · rw [left_rigid b bF d dF, at_b, right_rigid b bF d dF]
    · exact left_outward
    · exact outward
  have agree : Set.EqOn left right ({(a : Space), (b : Space), (d : Space)} : Set Space) := by
    rintro x (rfl | rfl | rfl)
    exacts [at_a, at_b, at_d]
  have spatial := P.no_three_collinear_vertices a.property b.property d.property
    (fun same => ab (Subtype.ext same)) (fun same => ad (Subtype.ext same)) (fun same => bd (Subtype.ext same))
  intro x member
  apply AffineMap.eqOn_affineSpan agree
  rw [F.triangle_spans_plane a b d aF bF dF spatial]
  exact subset_affineSpan ℝ F.val member

end SixVertexUnfolding.ConvexPolyhedron.Face
