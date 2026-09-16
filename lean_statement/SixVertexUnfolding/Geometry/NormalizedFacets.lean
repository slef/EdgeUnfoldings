import SixVertexUnfolding.Geometry.FacetHalfspaces
import SixVertexUnfolding.Geometry.Intersections

/-! Normalize each facet inequality to have value one, measured from an interior center. -/

namespace SixVertexUnfolding.ConvexPolyhedron

/-- This internal representation fixes the otherwise arbitrary scale of each supporting normal. -/
structure NormalizedFacets (P : ConvexPolyhedron) (center : Space) where
  normal : P.Face → Space
  support : ∀ F, ∀ x ∈ P.body, inner ℝ (normal F) (x - center) ≤ 1
  face_eq : ∀ F, F.val = {x ∈ P.body | inner ℝ (normal F) (x - center) = 1}

theorem exists_normalized_facets (P : ConvexPolyhedron) {center : Space}
    (inside : center ∈ interior P.body) : Nonempty (NormalizedFacets P center) := by
  have normalized (F : P.Face) : ∃ n : Space,
      (∀ x ∈ P.body, inner ℝ n (x - center) ≤ 1) ∧
      F.val = {x ∈ P.body | inner ℝ n (x - center) = 1} := by
    obtain ⟨n, level, nonzero, support, face_eq⟩ := F.property.2
    have gap_pos : 0 < level - inner ℝ n center :=
      sub_pos.mpr (P.strict_support_at_interior nonzero support inside)
    let scaled := (level - inner ℝ n center)⁻¹ • n
    have value (x : Space) : inner ℝ scaled (x - center) =
        (inner ℝ n x - inner ℝ n center) / (level - inner ℝ n center) := by
      simp only [scaled, real_inner_smul_left, inner_sub_right, div_eq_mul_inv]
      ring
    refine ⟨scaled, ?_, ?_⟩
    · intro x hx
      rw [value, div_le_one gap_pos]
      exact sub_le_sub_right (support x hx) _
    · rw [face_eq]
      ext x
      simp only [Set.mem_setOf_eq, value, div_eq_one_iff_eq gap_pos.ne']
      constructor <;> rintro ⟨hx, equal⟩ <;> exact ⟨hx, by linarith⟩
  choose normal support face_eq using normalized
  exact ⟨⟨normal, support, face_eq⟩⟩

namespace NormalizedFacets

variable {P : ConvexPolyhedron} {center : Space} (facets : NormalizedFacets P center)

theorem on_face (F : P.Face) {x : Space} (member : x ∈ F.val) :
    inner ℝ (facets.normal F) (x - center) = 1 := (facets.face_eq F ▸ member).2

theorem normal_injective : Function.Injective facets.normal := by
  intro F G same
  apply Subtype.ext
  rw [facets.face_eq F, facets.face_eq G, same]

/-- A normalized facet normal cannot lie strictly between two different facet normals. -/
theorem eq_of_normal_between (A B C : P.Face)
    (between : facets.normal B ∈ segment ℝ (facets.normal A) (facets.normal C))
    (distinct : B ≠ C) : B = A := by
  obtain ⟨s, t, s_nonnegative, t_nonnegative, sum_one, combination⟩ := between
  have s_positive : 0 < s := by
    by_contra nonpositive
    have zero : s = 0 := le_antisymm (not_lt.mp nonpositive) s_nonnegative
    have one : t = 1 := by linarith
    have same : facets.normal B = facets.normal C := by
      simpa only [zero, one, zero_smul, one_smul, zero_add] using combination.symm
    exact distinct (facets.normal_injective same)
  apply B.eq_of_subset A
  intro x hx
  rw [facets.face_eq A]
  refine ⟨B.subset_body hx, ?_⟩
  have at_B := facets.on_face B hx
  rw [← combination, inner_add_left, real_inner_smul_left, real_inner_smul_left] at at_B
  have at_A := facets.support A x (B.subset_body hx)
  have at_C := facets.support C x (B.subset_body hx)
  nlinarith [mul_le_mul_of_nonneg_left at_C t_nonnegative]

/-- Three different facet normals are never collinear after normalization at an interior point. -/
theorem no_three_collinear (A B C : P.Face) (ab : A ≠ B) (ac : A ≠ C) (bc : B ≠ C) :
    ¬ Collinear ℝ ({facets.normal A, facets.normal B, facets.normal C} : Set Space) := by
  intro collinear
  rcases collinear.wbtw_or_wbtw_or_wbtw with middle_B | middle_C | middle_A
  · exact ab (facets.eq_of_normal_between A B C middle_B.mem_segment bc).symm
  · exact bc (facets.eq_of_normal_between B C A middle_C.mem_segment ac.symm).symm
  · exact ac (facets.eq_of_normal_between C A B middle_A.mem_segment ab)

end NormalizedFacets
end SixVertexUnfolding.ConvexPolyhedron
