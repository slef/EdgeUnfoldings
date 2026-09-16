import SixVertexUnfolding.Geometry.EdgeJunctions
import SixVertexUnfolding.Geometry.NonvertexJunctions

/-! Global finiteness of branching targets follows from the finite source
lists for original faces and edges, together with the original vertex set. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- A junction is a target different from the source with at least three shortest routes. -/
def junctions (P : ConvexPolyhedron) (a : frontier P.body) : Set (frontier P.body) :=
  {b | a ≠ b ∧ ∃ f ∈ P.geodesicFiber a b, ∃ g ∈ P.geodesicFiber a b,
    ∃ h ∈ P.geodesicFiber a b, f ≠ g ∧ f ≠ h ∧ g ≠ h}

namespace SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- In the canonical models, finite route counts detect the explicitly defined junctions. -/
theorem junction_iff_route_count (a b : frontier P.body) (different : a ≠ b) :
    b ∈ P.junctions a ↔ 2 < Nat.card (P.geodesicFiber a b) := by
  change (a ≠ b ∧ ∃ f ∈ P.geodesicFiber a b, ∃ g ∈ P.geodesicFiber a b,
    ∃ h ∈ P.geodesicFiber a b, f ≠ g ∧ f ≠ h ∧ g ≠ h) ↔ _
  rw [and_iff_right different]
  exact (two_lt_ncard (graph.geodesicFiber_finite small_faces a b different)).symm

include graph small_faces in
/-- There are only finitely many targets with three or more shortest routes, on the entire surface. -/
theorem junctions_finite (a : frontier P.body) : (P.junctions a).Finite := by
  let face_targets (F : P.Face) : Set (frontier P.body) :=
    {b | a ≠ b ∧ (∀ G : P.Face, (b : Space) ∈ G.val → G = F) ∧
      2 < Nat.card (P.geodesicFiber a b)}
  let edge_targets (e : {pair : P.Face × P.Face // P.ShareEdge pair.1 pair.2}) : Set (frontier P.body) :=
    {b | a ≠ b ∧ (b : Space) ∈ e.val.1.val ∩ e.val.2.val ∧
      (b : Space) ∉ P.vertices ∧ 2 < Nat.card (P.geodesicFiber a b)}
  have faces_finite : (⋃ F, face_targets F).Finite :=
    finite_iUnion (fun F => graph.face_junctions_finite small_faces a F)
  have edges_finite : (⋃ e, edge_targets e).Finite :=
    finite_iUnion (fun e => graph.edge_junctions_finite small_faces a e.val.1 e.val.2 e.property)
  have vertices_finite := P.vertices.finite_toSet.preimage
    (f := fun b : frontier P.body => (b : Space)) Subtype.val_injective.injOn
  apply ((faces_finite.union edges_finite).union vertices_finite).subset
  intro b hb
  have count := (graph.junction_iff_route_count small_faces a b hb.1).mp hb
  by_cases vertex : (b : Space) ∈ P.vertices
  · exact Or.inr vertex
  · apply Or.inl
    rcases P.nonvertex_incident_facets b.property vertex with
      ⟨F, _, unique⟩ | ⟨F, G, shared, target, _⟩
    · exact Or.inl (mem_iUnion.mpr ⟨F, hb.1, unique, count⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨(F, G), shared⟩, hb.1, target, vertex, count⟩)

end SixVertexGraph
end SixVertexUnfolding.ConvexPolyhedron
