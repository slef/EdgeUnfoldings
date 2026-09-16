import SixVertexUnfolding.Geometry.EnlargeContact

/-!
The geometric face definition in the public statement covers the entire boundary.
The proof maximizes a finite set of contact vertices and tilts any contact of
dimension less than two. No combinatorial model of a surface is assumed.
-/

namespace SixVertexUnfolding.ConvexPolyhedron

/-- Among supporting planes through a boundary point, some contact vertices span a facet. -/
theorem exists_facet_support (P : ConvexPolyhedron) {x : Space}
    (boundary : x ∈ frontier P.body) :
    ∃ n : Space, n ≠ 0 ∧ P.SupportsAt n x ∧
      affineDimension (P.contactVertices n x : Set Space) = 2 := by
  classical
  let normals : Set Space := {n | n ≠ 0 ∧ P.SupportsAt n x}
  let contacts := fun n => P.contactVertices n x
  have some_normal : normals.Nonempty := P.supporting_plane_at_boundary boundary
  have finitely_many_contacts : (contacts '' normals).Finite := by
    apply P.vertices.powerset.finite_toSet.subset
    rintro _ ⟨n, _, rfl⟩
    exact Finset.mem_powerset.mpr (P.contactVertices_subset n x)
  obtain ⟨n, admissible, maximal⟩ :=
    finitely_many_contacts.exists_maximalFor' contacts normals some_normal
  obtain ⟨nonzero, support⟩ := admissible
  have point : x ∈ P.body := by
    simpa only [P.body_closed.closure_eq] using boundary.1
  have upper := P.contact_dimension_le_two n x nonzero
  have not_small : ¬ affineDimension (P.contactVertices n x : Set Space) ≤ 1 := by
    intro small
    obtain ⟨m, m_nonzero, m_support, larger⟩ := P.enlarge_contact n x nonzero support point small
    have reverse := maximal (show m ∈ normals from ⟨m_nonzero, m_support⟩) larger.1
    exact larger.2 reverse
  exact ⟨n, nonzero, support, by omega⟩

/-- Every boundary point belongs to a face as defined in the public statement. -/
theorem boundary_point_in_face (P : ConvexPolyhedron) {x : Space}
    (boundary : x ∈ frontier P.body) : ∃ F : P.Face, x ∈ F.val := by
  obtain ⟨n, nonzero, support, dimension⟩ := P.exists_facet_support boundary
  have point : x ∈ P.body := by
    simpa only [P.body_closed.closure_eq] using boundary.1
  have facet : P.IsFace (P.contactSet n x) := by
    refine ⟨?_, n, inner ℝ n x, nonzero, support, rfl⟩
    rw [P.contactSet_eq_convexHull n x support point, affineDimension_convexHull]
    exact dimension
  exact ⟨⟨P.contactSet n x, facet⟩, point, rfl⟩

/-- The surface of the convex solid is exactly the union of its facets. -/
theorem frontier_eq_union_faces (P : ConvexPolyhedron) :
    frontier P.body = ⋃ F : P.Face, F.val := by
  ext x
  constructor
  · intro boundary
    obtain ⟨F, hx⟩ := P.boundary_point_in_face boundary
    exact Set.mem_iUnion.mpr ⟨F, hx⟩
  · intro member
    obtain ⟨F, hx⟩ := Set.mem_iUnion.mp member
    exact F.subset_frontier hx

end SixVertexUnfolding.ConvexPolyhedron
