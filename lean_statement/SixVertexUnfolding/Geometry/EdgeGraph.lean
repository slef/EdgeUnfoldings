import SixVertexUnfolding.Geometry.ContactFacets

/-! The graph on original vertices, with adjacency certified by an entire shared edge. -/

namespace SixVertexUnfolding.ConvexPolyhedron

/-- Graph vertices are exactly the genuine vertices specified in the public definition. -/
abbrev Vertex (P : ConvexPolyhedron) := (P.vertices : Set Space)

/-- Two original vertices are adjacent when their segment is a whole shared facet edge. -/
def edgeGraph (P : ConvexPolyhedron) : SimpleGraph P.Vertex where
  Adj a b := a ≠ b ∧ ∃ F G : P.Face,
    P.ShareEdge F G ∧ F.val ∩ G.val = segment ℝ (a : Space) (b : Space)
  symm := by
    intro a b ⟨distinct, F, G, shared, edge_eq⟩
    exact ⟨distinct.symm, F, G, shared,
      edge_eq.trans (segment_symm ℝ (a : Space) (b : Space))⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

noncomputable instance edgeGraph_locallyFinite (P : ConvexPolyhedron) : P.edgeGraph.LocallyFinite :=
  fun _ => Fintype.ofFinite _

noncomputable instance edgeGraph_compl_locallyFinite (P : ConvexPolyhedron) :
    P.edgeGraphᶜ.LocallyFinite := fun _ => Fintype.ofFinite _

/-- The zero normal touches every vertex, so cannot have just two contact vertices. -/
theorem normal_ne_zero_of_contact_pair (P : ConvexPolyhedron) (a b : P.Vertex)
    (distinct : a ≠ b) (n : Space)
    (contacts : (P.contactVertices n a : Set Space) = {(a : Space), (b : Space)}) :
    n ≠ 0 := by
  intro zero
  subst n
  have all_vertices : P.contactVertices 0 a = P.vertices := by simp [contactVertices]
  rw [all_vertices] at contacts
  have distinct_points : (a : Space) ≠ (b : Space) := fun equal => distinct (Subtype.ext equal)
  have two : P.vertices.card = 2 := by
    have count := congrArg Set.ncard contacts
    simpa [Set.ncard_pair distinct_points] using count
  have lower := P.four_le_vertex_count
  omega

/-- A supporting plane whose contact vertices are exactly a and b certifies their original edge. -/
theorem edgeGraph_adj_of_contact_pair (P : ConvexPolyhedron) (a b : P.Vertex)
    (distinct : a ≠ b) (n : Space) (nonzero : n ≠ 0) (support : P.SupportsAt n a)
    (contacts : (P.contactVertices n a : Set Space) = {(a : Space), (b : Space)}) :
    P.edgeGraph.Adj a b := by
  have distinct_points : (a : Space) ≠ (b : Space) := fun equal => distinct (Subtype.ext equal)
  have dimension : affineDimension (P.contactVertices n a : Set Space) = 1 := by
    rw [contacts]
    exact affineDimension_pair distinct_points
  obtain ⟨F, G, shared, edge_eq⟩ := P.exists_facets_of_one_dimensional_contact
    n a nonzero support (P.vertices_subset_body a.property) dimension
  refine ⟨distinct, F, G, shared, ?_⟩
  rw [edge_eq, P.contactSet_eq_convexHull n a support (P.vertices_subset_body a.property),
    contacts, convexHull_pair]

end SixVertexUnfolding.ConvexPolyhedron
