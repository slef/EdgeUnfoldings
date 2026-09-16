import SixVertexUnfolding.Geometry.Faces
import SixVertexUnfolding.Geometry.AffineDimension

/-! Intersections of the original polygonal faces. -/

namespace SixVertexUnfolding.ConvexPolyhedron.Face

variable {P : ConvexPolyhedron} (F G : P.Face)

/-- Intersecting the solid with the affine plane of a facet recovers that whole facet. -/
theorem body_inter_affineSpan :
    P.body ∩ (affineSpan ℝ F.val : Set Space) = F.val := by
  obtain ⟨_, n, level, _, _, face_eq⟩ := F.property
  have agree : Set.EqOn (innerSL ℝ n).toLinearMap.toAffineMap
      (AffineMap.const ℝ Space level) F.val := by
    intro x hx
    exact (face_eq ▸ hx).2
  have agree_on_plane := AffineMap.eqOn_affineSpan agree
  apply Set.Subset.antisymm
  · rintro x ⟨hx, in_plane⟩
    rw [face_eq]
    exact ⟨hx, agree_on_plane in_plane⟩
  · intro x hx
    exact ⟨F.subset_body hx, subset_affineSpan ℝ F.val hx⟩

theorem eq_of_affineSpan_eq
    (same_plane : affineSpan ℝ F.val = affineSpan ℝ G.val) : F = G := by
  apply Subtype.ext
  rw [← F.body_inter_affineSpan, ← G.body_inter_affineSpan, same_plane]

/-- A whole facet cannot be properly contained in another whole facet. -/
theorem eq_of_subset (inclusion : F.val ⊆ G.val) : F = G :=
  F.eq_of_affineSpan_eq G (affineSpan_eq_of_subset_of_dimension_eq F.nonempty inclusion
    (F.property.1.trans G.property.1.symm))

/-- Distinct facets cannot have a two-dimensional intersection. -/
theorem intersection_dimension_le_one (distinct : F ≠ G) :
    affineDimension (F.val ∩ G.val) ≤ 1 := by
  have left_bound := affineDimension_mono (Set.inter_subset_left : F.val ∩ G.val ⊆ F.val)
  have right_bound := affineDimension_mono (Set.inter_subset_right : F.val ∩ G.val ⊆ G.val)
  have left_dimension := F.property.1
  have right_dimension := G.property.1
  by_contra too_large
  have intersection_dimension : affineDimension (F.val ∩ G.val) = 2 := by omega
  have nonempty := nonempty_of_affineDimension_pos (s := F.val ∩ G.val) (by omega)
  have left_span := affineSpan_eq_of_subset_of_dimension_eq nonempty
    Set.inter_subset_left (intersection_dimension.trans left_dimension.symm)
  have right_span := affineSpan_eq_of_subset_of_dimension_eq nonempty
    Set.inter_subset_right (intersection_dimension.trans right_dimension.symm)
  exact distinct (F.eq_of_affineSpan_eq G (left_span.symm.trans right_span))

theorem intersection_isExposed : IsExposed ℝ P.body (F.val ∩ G.val) :=
  F.isExposed.inter G.isExposed

/-- Shared points form the convex hull of the original vertices common to the two faces. -/
theorem intersection_eq_convexHull_vertices :
    F.val ∩ G.val = convexHull ℝ ((F.val ∩ G.val) ∩ (P.vertices : Set Space)) := by
  have extreme_eq := (F.intersection_isExposed G).isExtreme.extremePoints_eq
  rw [P.body_extreme_points] at extreme_eq
  have finite_vertices : ((F.val ∩ G.val).extremePoints ℝ).Finite := by
    rw [extreme_eq]
    exact P.vertices.finite_toSet.subset Set.inter_subset_right
  have hull_eq := closure_convexHull_extremePoints
    ((F.intersection_isExposed G).isCompact P.body_compact) (F.convex.inter G.convex)
  rw [(finite_vertices.isClosed_convexHull ℝ).closure_eq, extreme_eq] at hull_eq
  exact hull_eq.symm

end SixVertexUnfolding.ConvexPolyhedron.Face
