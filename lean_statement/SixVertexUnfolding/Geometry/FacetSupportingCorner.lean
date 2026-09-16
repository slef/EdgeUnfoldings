import SixVertexUnfolding.Geometry.FacetCornerCone

/-! The two neighboring supporting facets bound the full polygon at a corner. -/

namespace SixVertexUnfolding.ConvexPolyhedron.Face

variable {P : ConvexPolyhedron}

/-- A facet is contained in the corner cone between two of its original supporting hinges. -/
theorem placed_in_supporting_corner (F H K : P.Face) (place : Space →ᵃ[ℝ] Plane)
    (o a b : Space) (oF : o ∈ F.val) (aF : a ∈ F.val) (bF : b ∈ F.val)
    (oH : o ∈ H.val) (aH : a ∈ H.val) (bH : b ∉ H.val)
    (oK : o ∈ K.val) (bK : b ∈ K.val) (aK : a ∉ K.val)
    (noncollinear : ¬ Collinear ℝ ({o, a, b} : Set Space)) :
    place '' F.val ⊆ translatedCone (place o) (place a - place o) (place b - place o) := by
  obtain ⟨n, level, _, support, face_eq⟩ := H.property.2
  obtain ⟨m, other_level, _, other_support, other_eq⟩ := K.property.2
  have no := (face_eq ▸ oH).2
  have na := (face_eq ▸ aH).2
  have mo := (other_eq ▸ oK).2
  have mb := (other_eq ▸ bK).2
  have nb : inner ℝ n b < level := by
    apply lt_of_le_of_ne (support b (F.subset_body bF))
    intro equal
    exact bH (face_eq ▸ ⟨F.subset_body bF, equal⟩)
  have ma : inner ℝ m a < other_level := by
    apply lt_of_le_of_ne (other_support a (F.subset_body aF))
    intro equal
    exact aK (other_eq ▸ ⟨F.subset_body aF, equal⟩)
  apply F.placed_in_corner_cone place o a b
    (subset_affineSpan ℝ _ oF) (subset_affineSpan ℝ _ aF) (subset_affineSpan ℝ _ bF) noncollinear
    (innerSL ℝ n).toLinearMap (innerSL ℝ m).toLinearMap
  · change inner ℝ n (a - o) = 0
    rw [inner_sub_right, na, no, sub_self]
  · change inner ℝ n (b - o) < 0
    rw [inner_sub_right, no]
    linarith
  · change inner ℝ m (b - o) = 0
    rw [inner_sub_right, mb, mo, sub_self]
  · change inner ℝ m (a - o) < 0
    rw [inner_sub_right, mo]
    linarith
  · intro x hx
    change inner ℝ n (x - o) ≤ 0
    rw [inner_sub_right, no]
    exact sub_nonpos.mpr (support x (F.subset_body hx))
  · intro x hx
    change inner ℝ m (x - o) ≤ 0
    rw [inner_sub_right, mo]
    exact sub_nonpos.mpr (other_support x (F.subset_body hx))

end SixVertexUnfolding.ConvexPolyhedron.Face
