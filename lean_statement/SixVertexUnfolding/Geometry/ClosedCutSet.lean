import SixVertexUnfolding.Geometry.NonvertexRouteStability
import SixVertexUnfolding.Geometry.SourceNeighborhood

/-! The multiple-route set, augmented by original vertices other than the
source, is compact. Finite embedded-tree structure is a separate obligation. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- Multiple-route targets together with all original vertices other than the source. -/
def cutSet (P : ConvexPolyhedron) (a : frontier P.body) : Set (frontier P.body) :=
  {b | (b : Space) ∈ P.multipleRouteLocus a ∨ ((b : Space) ∈ P.vertices ∧ b ≠ a)}

theorem source_not_cutSet (P : ConvexPolyhedron) (a : frontier P.body) : a ∉ P.cutSet a := by
  rintro (multiple | vertex)
  · exact ((P.multiple_routes_iff_fiber a a).mp multiple).1 rfl
  · exact vertex.2 rfl

namespace SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- In canonical models, all limits of multiple-route points lie in the explicit cut set. -/
theorem closure_multiple_subset_cutSet (a : frontier P.body) :
    closure {b : frontier P.body | (b : Space) ∈ P.multipleRouteLocus a} ⊆ P.cutSet a := by
  intro b limit
  have different : a ≠ b := by
    rintro rfl
    exact P.source_not_closure_multiple_routes a limit
  by_cases vertex : (b : Space) ∈ P.vertices
  · exact Or.inr ⟨vertex, different.symm⟩
  · exact Or.inl (graph.multiple_routes_closed_nonvertex small_faces a b different vertex limit)

include graph small_faces in
/-- Adding precisely the original vertices other than the source makes the multiple-route set closed. -/
theorem cutSet_closed (a : frontier P.body) : IsClosed (P.cutSet a) := by
  let vertices : Set (frontier P.body) := {b | (b : Space) ∈ P.vertices ∧ b ≠ a}
  have finite : vertices.Finite :=
    (P.vertices.finite_toSet.preimage (f := fun b : frontier P.body => (b : Space)) Subtype.val_injective.injOn).subset
      (fun _ h => h.1)
  apply isClosed_of_closure_subset
  change closure ({b : frontier P.body | (b : Space) ∈ P.multipleRouteLocus a} ∪ vertices) ⊆ P.cutSet a
  rw [closure_union, finite.isClosed.closure_eq]
  exact union_subset (graph.closure_multiple_subset_cutSet small_faces a) (fun _ member => Or.inr member)

include graph small_faces in
/-- The explicit cut set is a compact subset of the actual boundary. -/
theorem cutSet_compact (a : frontier P.body) : IsCompact (P.cutSet a) := by
  letI : CompactSpace (frontier P.body) := isCompact_iff_compactSpace.mp
    (P.body_compact.of_isClosed_subset isClosed_frontier P.body_closed.frontier_subset)
  exact (graph.cutSet_closed small_faces a).isCompact

end SixVertexGraph
end SixVertexUnfolding.ConvexPolyhedron
