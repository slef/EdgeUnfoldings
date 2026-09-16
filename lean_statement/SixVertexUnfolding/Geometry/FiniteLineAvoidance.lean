import SixVertexUnfolding.Geometry.TriangleTopology

/-! An open planar overlap contains a point off any prescribed finite collection of lines. -/

namespace SixVertexUnfolding

/-- A nonempty open set cannot be contained in a proper affine subspace. -/
theorem open_set_minus_affine_subspace_nonempty (u : Set Plane) (open_u : IsOpen u)
    (nonempty : u.Nonempty) (a : AffineSubspace ℝ Plane) (proper : a ≠ ⊤) :
    (u \ (a : Set Plane)).Nonempty := by
  by_contra! empty
  have contained : u ⊆ (a : Set Plane) := by
    intro x member
    by_contra outside
    have in_difference : x ∈ u \ (a : Set Plane) := ⟨member, outside⟩
    rwa [empty] at in_difference
  have spans := open_u.affineSpan_eq_top nonempty
  have bound := (affineSpan_le.mpr contained : affineSpan ℝ u ≤ a)
  rw [spans] at bound
  exact proper (top_unique bound)

/-- Removing finitely many proper affine subspaces leaves an available point. -/
theorem exists_point_avoiding_affine_subspaces (obstacles : Finset (AffineSubspace ℝ Plane))
    (proper : ∀ a ∈ obstacles, a ≠ ⊤) (u : Set Plane) (open_u : IsOpen u) (nonempty : u.Nonempty) :
    ∃ x ∈ u, ∀ a ∈ obstacles, x ∉ a := by
  classical
  induction obstacles using Finset.induction_on generalizing u with
  | empty =>
    obtain ⟨x, member⟩ := nonempty
    exact ⟨x, member, by simp⟩
  | @insert a obstacles absent ih =>
    have available := open_set_minus_affine_subspace_nonempty u open_u nonempty a
      (proper a (Finset.mem_insert_self _ _))
    obtain ⟨x, member, avoids⟩ := ih
      (fun b hb => proper b (Finset.mem_insert_of_mem hb)) (u \ (a : Set Plane))
      (open_u.inter a.closed_of_finiteDimensional.isOpen_compl) available
    refine ⟨x, member.1, ?_⟩
    intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact member.2
    · exact avoids b hb

/-- A line through two planar points is proper, also when the two points coincide. -/
theorem planar_line_ne_top (a b : Plane) : affineSpan ℝ ({a, b} : Set Plane) ≠ ⊤ := by
  intro whole
  have bound := (collinear_pair ℝ a b).finrank_le_one
  have direction := congrArg AffineSubspace.direction whole
  rw [direction_affineSpan, AffineSubspace.direction_top] at direction
  rw [direction] at bound
  norm_num [Plane] at bound

/-- This supplies the manuscript's generic point without any generic-position assumption. -/
theorem exists_point_avoiding_lines (lines : Finset (Plane × Plane))
    (u : Set Plane) (open_u : IsOpen u) (nonempty : u.Nonempty) :
    ∃ x ∈ u, ∀ endpoints ∈ lines,
      x ∉ affineSpan ℝ ({endpoints.1, endpoints.2} : Set Plane) := by
  classical
  let obstacles := lines.image (fun endpoints => affineSpan ℝ ({endpoints.1, endpoints.2} : Set Plane))
  have proper : ∀ a ∈ obstacles, a ≠ ⊤ := by
    intro a member
    obtain ⟨endpoints, _, rfl⟩ := Finset.mem_image.mp member
    exact planar_line_ne_top _ _
  obtain ⟨x, member, avoids⟩ := exists_point_avoiding_affine_subspaces obstacles proper u open_u nonempty
  exact ⟨x, member, fun endpoints h => avoids _ (Finset.mem_image_of_mem _ h)⟩

end SixVertexUnfolding
