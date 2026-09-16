import SixVertexUnfolding.Geometry.PocketContainment

/-! A connected interior is the component of the frontier complement that contains an interior seed. -/

namespace SixVertexUnfolding

/-- An interior seed identifies the interior component of a closed region. -/
theorem closed_region_interior_component (region : Set Plane)
    (closed : IsClosed region) (connected : IsPreconnected (interior region))
    (seed : Plane) (inside : seed ∈ interior region) :
    connectedComponentIn (frontier region)ᶜ seed = interior region := by
  have off_boundary : interior region ⊆ (frontier region)ᶜ := by
    intro x member on_boundary
    exact on_boundary.2 member
  have cover : (frontier region)ᶜ ⊆ interior region ∪ regionᶜ := by
    intro x avoids
    by_cases belongs : x ∈ region
    · left
      by_contra not_inside
      apply avoids
      rw [closed.frontier_eq]
      exact ⟨belongs, not_inside⟩
    · exact Or.inr belongs
  have disjoint : Disjoint (interior region) regionᶜ :=
    Set.disjoint_left.mpr (fun _ member outside => outside (interior_subset member))
  have component_cover := (connectedComponentIn_subset (frontier region)ᶜ seed).trans cover
  rcases isPreconnected_connectedComponentIn.subset_or_subset isOpen_interior closed.isOpen_compl
      disjoint component_cover with belongs | outside
  · exact Set.Subset.antisymm belongs (connected.subset_connectedComponentIn inside off_boundary)
  · exact False.elim (outside (mem_connectedComponentIn (off_boundary inside)) (interior_subset inside))

end SixVertexUnfolding
