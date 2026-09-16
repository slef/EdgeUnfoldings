import SixVertexUnfolding.Geometry.PocketContainment

/-! A connected set avoiding a closed region's frontier stays on one side. -/

namespace SixVertexUnfolding

/-- Boundary avoidance divides a connected set into exactly one of the two open sides. -/
theorem preconnected_set_on_one_side (region points : Set Plane)
    (closed : IsClosed region) (connected : IsPreconnected points)
    (safe : Disjoint points (frontier region)) : points ⊆ interior region ∨ points ⊆ regionᶜ := by
  have cover : points ⊆ interior region ∪ regionᶜ := by
    intro x member
    by_cases belongs : x ∈ region
    · left
      by_contra not_inside
      have boundary : x ∈ frontier region := by
        rw [closed.frontier_eq]
        exact ⟨belongs, not_inside⟩
      exact Set.disjoint_left.mp safe member boundary
    · exact Or.inr belongs
  exact connected.subset_or_subset isOpen_interior closed.isOpen_compl
    (Set.disjoint_left.mpr (fun _ inside outside => outside (interior_subset inside))) cover

/-- One interior seed propagates across a connected set that avoids the frontier. -/
theorem preconnected_set_in_region (region points : Set Plane)
    (closed : IsClosed region) (connected : IsPreconnected points)
    (safe : Disjoint points (frontier region)) (seed : Plane)
    (member : seed ∈ points) (inside : seed ∈ interior region) : points ⊆ interior region := by
  rcases preconnected_set_on_one_side region points closed connected safe with within | outside
  · exact within
  · exact False.elim (outside member (interior_subset inside))

end SixVertexUnfolding
