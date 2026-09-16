import SixVertexUnfolding.CanonicalSixGraphs

/-! Explicit candidate and actual facet vertex sets for the four six-vertex graphs. -/

namespace SixVertexUnfolding.SmallGraphs.SixGraphKind

/-- The original edges in the canonical labeling. -/
def adjacent (kind : SixGraphKind) (i j : Fin 6) : Prop :=
  i ≠ j ∧ s(i, j) ∉ kind.missingEdges

instance (kind : SixGraphKind) : DecidableRel kind.adjacent := fun _ _ => inferInstanceAs
  (Decidable (_ ≠ _ ∧ _ ∉ kind.missingEdges))

/-- A triangle is complete; a quadrilateral has exactly two neighbors at each corner. -/
def isPolygon (kind : SixGraphKind) (vertices : Finset (Fin 6)) : Prop :=
  (vertices.card = 3 ∧ ∀ a ∈ vertices, ∀ b ∈ vertices, a ≠ b → kind.adjacent a b) ∨
  (vertices.card = 4 ∧ ∀ a ∈ vertices, (vertices.filter (kind.adjacent a)).card = 2)

instance (kind : SixGraphKind) (vertices : Finset (Fin 6)) : Decidable (kind.isPolygon vertices) :=
  inferInstanceAs (Decidable ((_ ∧ _) ∨ (_ ∧ _)))

/-- All triangles and induced quadrilaterals of each graph, including potential nonfacial cycles. -/
def candidates : SixGraphKind → Finset (Finset (Fin 6))
  | .octahedron => {{0, 2, 4}, {0, 2, 5}, {0, 3, 4}, {0, 3, 5},
      {1, 2, 4}, {1, 2, 5}, {1, 3, 4}, {1, 3, 5}, {0, 1, 2, 3}, {0, 1, 4, 5}, {2, 3, 4, 5}}
  | .minusEdge => {{0, 2, 4}, {0, 2, 5}, {0, 3, 4}, {0, 3, 5},
      {1, 3, 4}, {1, 3, 5}, {0, 1, 4, 5}, {1, 2, 4, 5}, {2, 3, 4, 5}}
  | .prismDiagonal => {{0, 2, 4}, {0, 2, 5}, {0, 3, 5}, {1, 3, 5},
      {0, 1, 3, 4}, {0, 1, 4, 5}, {1, 2, 4, 5}}
  | .prism => {{0, 2, 4}, {1, 3, 5}, {0, 1, 3, 4}, {0, 2, 3, 5}, {1, 2, 4, 5}}

/-- The vertex sets of the original facets; auxiliary diagonals are not edges here. -/
def facets : SixGraphKind → Finset (Finset (Fin 6))
  | .octahedron => {{0, 2, 4}, {0, 2, 5}, {0, 3, 4}, {0, 3, 5},
      {1, 2, 4}, {1, 2, 5}, {1, 3, 4}, {1, 3, 5}}
  | .minusEdge => {{0, 2, 4}, {0, 2, 5}, {0, 3, 4}, {0, 3, 5},
      {1, 3, 4}, {1, 3, 5}, {1, 2, 4, 5}}
  | .prismDiagonal => {{0, 2, 4}, {0, 2, 5}, {0, 3, 5}, {1, 3, 5}, {0, 1, 3, 4}, {1, 2, 4, 5}}
  | .prism => {{0, 2, 4}, {1, 3, 5}, {0, 1, 3, 4}, {0, 2, 3, 5}, {1, 2, 4, 5}}

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- Exhaust the 64 subsets of the six original vertices, using ordinary kernel reduction. -/
theorem isPolygon_iff_candidate : ∀ (kind : SixGraphKind) (vertices : Finset (Fin 6)),
    kind.isPolygon vertices ↔ vertices ∈ kind.candidates := by decide

end SixVertexUnfolding.SmallGraphs.SixGraphKind
