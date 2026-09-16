import SixVertexUnfolding.Geometry.FacetCoordinates
import SixVertexUnfolding.Geometry.HingeSides

/-!
A supporting facet puts every point of its neighboring base on the same side
of their hinge. The statement remains true after any affine placement.
-/

namespace SixVertexUnfolding

/-- Perpendicular hinge components respect affine coordinates based at a hinge endpoint. -/
theorem hingeSideVector_of_coordinates (place : Space →ᵃ[ℝ] Plane) (a b c x : Space)
    (t u : ℝ) (coordinates : x - a = t • (b - a) + u • (c - a))
    (distinct : place a ≠ place b) :
    hingeSideVector (place a) (place b) (place x) =
      u • hingeSideVector (place a) (place b) (place c) := by
  have flat := congrArg place.linear coordinates
  have map_difference (v w : Space) : place.linear (v - w) = place v - place w :=
    place.linearMap_vsub v w
  simp only [map_add, map_smul, map_difference] at flat
  have edge_zero := hingeSideVector_right (place a) (place b) distinct
  let axis := NormedSpace.normalize (place b - place a)
  have additive (v w : Plane) : hingeRemainder axis (v + w) =
      hingeRemainder axis v + hingeRemainder axis w := by
    simp only [hingeRemainder, inner_add_right, add_smul]
    module
  have scaled (r : ℝ) (v : Plane) : hingeRemainder axis (r • v) = r • hingeRemainder axis v := by
    simp only [hingeRemainder, inner_smul_right, mul_smul, smul_sub]
  change hingeRemainder axis (place x - place a) = u • hingeRemainder axis (place c - place a)
  rw [flat, additive, scaled, scaled]
  change t • hingeSideVector (place a) (place b) (place b) +
    u • hingeSideVector (place a) (place b) (place c) = _
  rw [edge_zero, smul_zero, zero_add]
  rfl

namespace ConvexPolyhedron.Face

variable {P : ConvexPolyhedron} (base side : P.Face)

/-- Relative to a supporting hinge, every base point has a nonnegative transverse coordinate. -/
theorem exists_nonnegative_hinge_coordinates (a b c x : Space)
    (aB : a ∈ base.val) (bB : b ∈ base.val) (cB : c ∈ base.val) (xB : x ∈ base.val)
    (aS : a ∈ side.val) (bS : b ∈ side.val) (cS : c ∉ side.val)
    (noncollinear : ¬ Collinear ℝ ({a, b, c} : Set Space)) :
    ∃ t u : ℝ, 0 ≤ u ∧ x - a = t • (b - a) + u • (c - a) := by
  obtain ⟨t, u, coordinates⟩ := base.exists_triangle_coordinates a b c x aB bB cB xB noncollinear
  obtain ⟨_, n, level, _, support, face_eq⟩ := side.property
  have a_height := (face_eq ▸ aS).2
  have b_height := (face_eq ▸ bS).2
  have c_height : inner ℝ n c < level := by
    apply lt_of_le_of_ne (support c (base.subset_body cB))
    intro same
    exact cS (face_eq ▸ ⟨base.subset_body cB, same⟩)
  have x_height := support x (base.subset_body xB)
  have height_coordinates := congrArg (fun v => inner ℝ n v) coordinates
  simp only [inner_sub_right, inner_add_right, inner_smul_right, a_height, b_height,
    sub_self, mul_zero, zero_add] at height_coordinates
  refine ⟨t, u, ?_, coordinates⟩
  by_contra negative
  have positive := mul_pos_of_neg_of_neg (lt_of_not_ge negative) (sub_neg.mpr c_height)
  linarith

/-- All placed base points lie on the same closed side of the hinge as a chosen third vertex. -/
theorem placed_hinge_side (place : Space →ᵃ[ℝ] Plane) (a b c x : Space)
    (aB : a ∈ base.val) (bB : b ∈ base.val) (cB : c ∈ base.val) (xB : x ∈ base.val)
    (aS : a ∈ side.val) (bS : b ∈ side.val) (cS : c ∉ side.val)
    (noncollinear : ¬ Collinear ℝ ({a, b, c} : Set Space)) (distinct : place a ≠ place b) :
    ∃ u : ℝ, 0 ≤ u ∧ hingeSideVector (place a) (place b) (place x) =
      u • hingeSideVector (place a) (place b) (place c) := by
  obtain ⟨t, u, nonnegative, coordinates⟩ :=
    base.exists_nonnegative_hinge_coordinates side a b c x aB bB cB xB aS bS cS noncollinear
  exact ⟨u, nonnegative, hingeSideVector_of_coordinates place a b c x t u coordinates distinct⟩

end ConvexPolyhedron.Face
end SixVertexUnfolding
