import SixVertexUnfolding.Geometry.BoundaryBarrier

/-! Boundary avoidance prevents a convex triangle from entering another face. -/

namespace SixVertexUnfolding

/-- A convex region with an exterior point cannot enter a closed region while its interior avoids the boundary. -/
theorem disjoint_interiors_of_boundary_disjoint (base other : Set Plane)
    (base_closed : IsClosed base) (other_convex : Convex ℝ other)
    (other_interior : (interior other).Nonempty) (outside : ¬ other ⊆ base)
    (misses_boundary : Disjoint (interior other) (frontier base)) :
    Disjoint (interior base) (interior other) := by
  have inside_or_outside : interior other ⊆ interior base ∪ baseᶜ := by
    intro x x_other
    by_cases x_base : x ∈ base
    · left
      by_contra not_inside
      have boundary : x ∈ frontier base := by
        rw [base_closed.frontier_eq]
        exact ⟨x_base, not_inside⟩
      exact Set.disjoint_left.mp misses_boundary x_other boundary
    · exact Or.inr x_base
  have regions_disjoint : Disjoint (interior base) baseᶜ :=
    Set.disjoint_left.mpr (fun _ inside outside => outside (interior_subset inside))
  rcases (other_convex.interior.isPreconnected).subset_or_subset isOpen_interior
      base_closed.isOpen_compl regions_disjoint inside_or_outside with inside | disjoint
  · apply False.elim
    apply outside
    calc
      other ⊆ closure other := subset_closure
      _ = closure (interior other) :=
        (other_convex.closure_interior_eq_closure_of_nonempty_interior other_interior).symm
      _ ⊆ closure base := closure_mono (inside.trans interior_subset)
      _ = base := base_closed.closure_eq
  · exact Set.disjoint_left.mpr (fun _ inside other => disjoint other (interior_subset inside))

end SixVertexUnfolding
