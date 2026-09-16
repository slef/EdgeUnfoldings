import SixVertexUnfolding.Geometry.BoundaryExclusion

/-! A single interior seed identifies the correct side of a closed pocket boundary. -/

namespace SixVertexUnfolding

/-- A convex face whose interior avoids the pocket frontier lies inside once one interior point does. -/
theorem convex_face_in_closed_region (region face : Set Plane)
    (closed : IsClosed region) (convex : Convex ℝ face)
    (regular : closure (interior face) = face)
    (safe : Disjoint (interior face) (frontier region))
    (seed : Plane) (in_face : seed ∈ interior face) (in_region : seed ∈ interior region) :
    face ⊆ region := by
  have inside_or_outside : interior face ⊆ interior region ∪ regionᶜ := by
    intro x member
    by_cases belongs : x ∈ region
    · left
      by_contra not_inside
      have on_boundary : x ∈ frontier region := by
        rw [closed.frontier_eq]
        exact ⟨belongs, not_inside⟩
      exact Set.disjoint_left.mp safe member on_boundary
    · exact Or.inr belongs
  have disjoint : Disjoint (interior region) regionᶜ :=
    Set.disjoint_left.mpr (fun _ inside outside => outside (interior_subset inside))
  rcases convex.interior.isPreconnected.subset_or_subset isOpen_interior closed.isOpen_compl
      disjoint inside_or_outside with inside | outside
  · rw [← regular]
    exact (closure_mono (inside.trans interior_subset)).trans_eq closed.closure_eq
  · exact False.elim (outside in_face (interior_subset in_region))

end SixVertexUnfolding
