import SixVertexUnfolding.Geometry.Intersections

/-! Coordinates in a facet plane, anchored at three noncollinear points. -/

namespace SixVertexUnfolding.ConvexPolyhedron.Face

variable {P : ConvexPolyhedron} (F : P.Face)

/-- Three noncollinear points on a facet span its entire plane. -/
theorem triangle_spans_plane (a b c : Space) (aF : a ∈ F.val) (bF : b ∈ F.val)
    (cF : c ∈ F.val) (noncollinear : ¬ Collinear ℝ ({a, b, c} : Set Space)) :
    affineSpan ℝ ({a, b, c} : Set Space) = affineSpan ℝ F.val := by
  have inclusion : ({a, b, c} : Set Space) ⊆ F.val := by
    rintro x (rfl | rfl | rfl)
    exacts [aF, bF, cF]
  have upper := affineDimension_mono inclusion
  have lower : ¬ affineDimension ({a, b, c} : Set Space) ≤ 1 := by
    intro small
    apply noncollinear
    apply collinear_iff_finrank_le_one.mpr
    change Module.finrank ℝ (affineSpan ℝ ({a, b, c} : Set Space)).direction ≤ 1 at small
    rwa [direction_affineSpan] at small
  apply affineSpan_eq_of_subset_of_dimension_eq (by simp) inclusion
  rw [F.property.1] at upper ⊢
  omega

/-- Every facet point has two real coordinates along an edge and toward a third point. -/
theorem exists_triangle_coordinates (a b c x : Space)
    (aF : a ∈ F.val) (bF : b ∈ F.val) (cF : c ∈ F.val) (xF : x ∈ F.val)
    (noncollinear : ¬ Collinear ℝ ({a, b, c} : Set Space)) :
    ∃ t u : ℝ, x - a = t • (b - a) + u • (c - a) := by
  have x_span : x ∈ affineSpan ℝ ({a, b, c} : Set Space) := by
    rw [F.triangle_spans_plane a b c aF bF cF noncollinear]
    exact subset_affineSpan ℝ F.val xF
  have a_span := subset_affineSpan ℝ ({a, b, c} : Set Space) (by simp : a ∈ ({a, b, c} : Set Space))
  have difference := vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan x_span a_span
  rw [vectorSpan_eq_span_vsub_set_right ℝ (by simp : a ∈ ({a, b, c} : Set Space))] at difference
  simp only [Set.image_insert_eq, Set.image_singleton, vsub_eq_sub, sub_self,
    Submodule.span_insert_zero] at difference
  obtain ⟨t, u, equal⟩ := Submodule.mem_span_pair.mp difference
  exact ⟨t, u, equal.symm⟩

/-- A point of the solid outside a facet also lies outside that facet's plane. -/
theorem outside_affineSpan {x : Space} (body : x ∈ P.body) (outside : x ∉ F.val) :
    x ∉ affineSpan ℝ F.val := by
  intro in_plane
  apply outside
  rw [← F.body_inter_affineSpan]
  exact ⟨body, in_plane⟩

end SixVertexUnfolding.ConvexPolyhedron.Face
