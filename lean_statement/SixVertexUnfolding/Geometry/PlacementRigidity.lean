import SixVertexUnfolding.Geometry.Faces

/-!
For an affine placement, checking distances between the original vertices is
enough to establish rigidity on the entire polygon. The proof extends the Gram
matrix equality from generating differences to their linear span.
-/

namespace SixVertexUnfolding

/-- Equality of inner products on generators extends by linearity in both arguments. -/
theorem linear_preserves_inner_on_span (L : Space →ₗ[ℝ] Plane) (s : Set Space)
    (generators : ∀ u ∈ s, ∀ v ∈ s, inner ℝ (L u) (L v) = inner ℝ u v) :
    ∀ u ∈ Submodule.span ℝ s, ∀ v ∈ Submodule.span ℝ s,
      inner ℝ (L u) (L v) = inner ℝ u v := by
  have extend_right (u : Space) (hu : u ∈ s) :
      ∀ v ∈ Submodule.span ℝ s, inner ℝ (L u) (L v) = inner ℝ u v := by
    have agree : Set.EqOn ((innerSL ℝ (L u)).toLinearMap.comp L)
        (innerSL ℝ u).toLinearMap s := generators u hu
    exact fun _ hv => LinearMap.eqOn_span agree hv
  intro u hu v hv
  have agree : Set.EqOn ((innerSL ℝ (L v)).toLinearMap.comp L)
      (innerSL ℝ v).toLinearMap s := by
    intro w hw
    change inner ℝ (L v) (L w) = inner ℝ v w
    rw [real_inner_comm (L w) (L v), real_inner_comm w v]
    exact extend_right w hw v hv
  have equal := LinearMap.eqOn_span agree hu
  change inner ℝ (L v) (L u) = inner ℝ v u at equal
  simpa only [real_inner_comm] using equal

/-- Pairwise distances determine an affine placement's rigidity on the whole affine span. -/
theorem affine_rigid_on_span_of_distances (place : Space →ᵃ[ℝ] Plane)
    (s : Set Space) (nonempty : s.Nonempty)
    (distances : ∀ u ∈ s, ∀ v ∈ s, dist (place u) (place v) = dist u v) :
    ∀ x ∈ affineSpan ℝ s, ∀ y ∈ affineSpan ℝ s,
      dist (place x) (place y) = dist x y := by
  obtain ⟨a, ha⟩ := nonempty
  let differences : Set Space := (fun v => v - a) '' s
  have map_difference (u v : Space) :
      place.linear (u - v) = place u - place v := place.linearMap_vsub u v
  have gram : ∀ u ∈ differences, ∀ v ∈ differences,
      inner ℝ (place.linear u) (place.linear v) = inner ℝ u v := by
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    rw [map_difference, map_difference]
    have norm_u := distances u hu a ha
    have norm_v := distances v hv a ha
    have norm_uv := distances u hu v hv
    simp only [dist_eq_norm] at norm_u norm_v norm_uv
    have source := norm_sub_sq_real (u - a) (v - a)
    have image := norm_sub_sq_real (place u - place a) (place v - place a)
    simp only [sub_sub_sub_cancel_right] at source image
    rw [norm_u, norm_v, norm_uv] at image
    linarith
  intro x hx y hy
  have difference_in_span := vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan hx hy
  rw [vectorSpan_eq_span_vsub_set_right ℝ ha] at difference_in_span
  have norm_squared := linear_preserves_inner_on_span place.linear differences gram
    (x - y) difference_in_span (x - y) difference_in_span
  simp only [real_inner_self_eq_norm_sq] at norm_squared
  have norm_equal := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp norm_squared
  simpa only [map_difference, dist_eq_norm] using norm_equal

namespace ConvexPolyhedron.Face

variable {P : ConvexPolyhedron} (F : P.Face)

/-- The rigid-placement obligation can be checked using only pairs of original face vertices. -/
theorem rigid_of_vertex_distances (place : Space →ᵃ[ℝ] Plane)
    (distances : ∀ x ∈ F.val ∩ (P.vertices : Set Space),
      ∀ y ∈ F.val ∩ (P.vertices : Set Space), dist (place x) (place y) = dist x y) :
    ∀ x ∈ F.val, ∀ y ∈ F.val, dist (place x) (place y) = dist x y := by
  have hull_nonempty := F.nonempty
  rw [F.eq_convexHull_vertices] at hull_nonempty
  have nonempty := convexHull_nonempty_iff.mp hull_nonempty
  have rigid := affine_rigid_on_span_of_distances place _ nonempty distances
  intro x hx y hy
  rw [F.eq_convexHull_vertices] at hx hy
  exact rigid x (convexHull_subset_affineSpan _ hx) y (convexHull_subset_affineSpan _ hy)

end ConvexPolyhedron.Face
end SixVertexUnfolding
