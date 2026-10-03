import SixVertexUnfolding.Geometry.FacetHingeSides

/-! Two original edges bounding a face corner place the whole convex face
inside the nonnegative cone of their directions. -/

namespace SixVertexUnfolding.ConvexPolyhedron.Face

variable {P : ConvexPolyhedron}

/-- Both corner coordinates are nonnegative, by the supporting facets at its two edges. -/
theorem nonnegative_corner_coordinates_of_facets (F leftSide rightSide : P.Face) (a b c x : Space)
    (aF : a ∈ F.val) (bF : b ∈ F.val) (cF : c ∈ F.val) (xF : x ∈ F.val)
    (aL : a ∈ leftSide.val) (bL : b ∈ leftSide.val) (cL : c ∉ leftSide.val)
    (aR : a ∈ rightSide.val) (cR : c ∈ rightSide.val) (bR : b ∉ rightSide.val)
    (noncollinear : ¬ Collinear ℝ ({a, b, c} : Set Space)) :
    ∃ t u : ℝ, 0 ≤ t ∧ 0 ≤ u ∧ x - a = t • (b - a) + u • (c - a) := by
  obtain ⟨t, u, hu, coordinates⟩ :=
    F.exists_nonnegative_hinge_coordinates leftSide a b c x aF bF cF xF aL bL cL noncollinear
  obtain ⟨_, n, level, _, support, face_eq⟩ := rightSide.property
  have a_height := (face_eq ▸ aR).2
  have c_height := (face_eq ▸ cR).2
  have b_height : inner ℝ n b < level := by
    apply lt_of_le_of_ne (support b (F.subset_body bF))
    intro same
    exact bR (face_eq ▸ ⟨F.subset_body bF, same⟩)
  have x_height := support x (F.subset_body xF)
  have height_coordinates := congrArg (fun v => inner ℝ n v) coordinates
  simp only [inner_sub_right, inner_add_right, inner_smul_right, a_height, c_height,
    sub_self, mul_zero, add_zero] at height_coordinates
  refine ⟨t, u, ?_, hu, coordinates⟩
  by_contra negative
  have positive := mul_pos_of_neg_of_neg (lt_of_not_ge negative) (sub_neg.mpr b_height)
  linarith

end SixVertexUnfolding.ConvexPolyhedron.Face
