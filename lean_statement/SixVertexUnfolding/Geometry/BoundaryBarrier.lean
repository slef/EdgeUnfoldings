import SixVertexUnfolding.Definitions

/-! Neighbors covering a face boundary prevent another convex face from entering it. -/

namespace SixVertexUnfolding

/-- A convex face cannot cross a covered boundary while avoiding the covering faces' interiors. -/
theorem disjoint_interiors_of_boundary_cover (base other : Set Plane) (neighbors : Fin 3 → Set Plane)
    (base_closed : IsClosed base) (other_convex : Convex ℝ other)
    (other_interior : (interior other).Nonempty) (outside : ¬ other ⊆ base)
    (regular : ∀ i, closure (interior (neighbors i)) = neighbors i)
    (covered : frontier base ⊆ ⋃ i, neighbors i)
    (safe : ∀ i, Disjoint (interior other) (interior (neighbors i))) :
    Disjoint (interior base) (interior other) := by
  have misses_boundary : Disjoint (interior other) (frontier base) := by
    apply Set.disjoint_left.mpr
    intro x x_other x_boundary
    obtain ⟨i, xi⟩ := Set.mem_iUnion.mp (covered x_boundary)
    have misses := (safe i).closure_right isOpen_interior
    rw [regular i] at misses
    exact Set.disjoint_left.mp misses x_other xi
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
