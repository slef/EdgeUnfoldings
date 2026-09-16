import SixVertexUnfolding.PairedGraphCases

/-! The four canonical graph forms in the six-vertex case without a universal vertex. -/

namespace SixVertexUnfolding.SmallGraphs

/-- Names for the four remaining original vertex-edge graphs. -/
inductive SixGraphKind where
  | octahedron
  | minusEdge
  | prismDiagonal
  | prism
  deriving DecidableEq, Fintype

/-- The complementary edges: three pairs, a four-vertex path and a pair, a six-vertex path, or a six-cycle. -/
def SixGraphKind.missingEdges : SixGraphKind → Finset (Sym2 (Fin 6))
  | .octahedron => {s(0, 1), s(2, 3), s(4, 5)}
  | .minusEdge => {s(0, 1), s(1, 2), s(2, 3), s(4, 5)}
  | .prismDiagonal => {s(0, 1), s(1, 2), s(2, 3), s(3, 4), s(4, 5)}
  | .prism => {s(0, 1), s(1, 2), s(2, 3), s(3, 4), s(4, 5), s(0, 5)}

/-- A canonical type and a relabeling for each of the 45 permitted extra-edge patterns. -/
def pairedGraphChoices : Fin 45 → SixGraphKind × (Fin 6 → Fin 6) :=
  ![(.octahedron, ![0, 1, 2, 3, 4, 5]),
    (.minusEdge, ![1, 0, 2, 3, 4, 5]),
    (.minusEdge, ![1, 0, 3, 2, 4, 5]),
    (.minusEdge, ![1, 0, 4, 5, 2, 3]),
    (.minusEdge, ![1, 0, 5, 4, 2, 3]),
    (.minusEdge, ![0, 1, 2, 3, 4, 5]),
    (.minusEdge, ![0, 1, 3, 2, 4, 5]),
    (.minusEdge, ![0, 1, 4, 5, 2, 3]),
    (.minusEdge, ![0, 1, 5, 4, 2, 3]),
    (.minusEdge, ![3, 2, 4, 5, 0, 1]),
    (.minusEdge, ![3, 2, 5, 4, 0, 1]),
    (.minusEdge, ![2, 3, 4, 5, 0, 1]),
    (.minusEdge, ![2, 3, 5, 4, 0, 1]),
    (.prismDiagonal, ![3, 2, 0, 1, 4, 5]),
    (.prismDiagonal, ![3, 2, 0, 1, 5, 4]),
    (.prismDiagonal, ![1, 0, 2, 3, 4, 5]),
    (.prismDiagonal, ![1, 0, 2, 3, 5, 4]),
    (.prismDiagonal, ![2, 3, 0, 1, 4, 5]),
    (.prismDiagonal, ![2, 3, 0, 1, 5, 4]),
    (.prismDiagonal, ![1, 0, 3, 2, 4, 5]),
    (.prismDiagonal, ![1, 0, 3, 2, 5, 4]),
    (.prismDiagonal, ![3, 2, 1, 0, 4, 5]),
    (.prismDiagonal, ![2, 3, 1, 0, 4, 5]),
    (.prismDiagonal, ![1, 0, 4, 5, 2, 3]),
    (.prismDiagonal, ![1, 0, 4, 5, 3, 2]),
    (.prismDiagonal, ![3, 2, 1, 0, 5, 4]),
    (.prismDiagonal, ![2, 3, 1, 0, 5, 4]),
    (.prismDiagonal, ![1, 0, 5, 4, 2, 3]),
    (.prismDiagonal, ![1, 0, 5, 4, 3, 2]),
    (.prismDiagonal, ![0, 1, 2, 3, 4, 5]),
    (.prismDiagonal, ![0, 1, 2, 3, 5, 4]),
    (.prismDiagonal, ![0, 1, 3, 2, 4, 5]),
    (.prismDiagonal, ![0, 1, 3, 2, 5, 4]),
    (.prismDiagonal, ![0, 1, 4, 5, 2, 3]),
    (.prismDiagonal, ![0, 1, 4, 5, 3, 2]),
    (.prismDiagonal, ![0, 1, 5, 4, 2, 3]),
    (.prismDiagonal, ![0, 1, 5, 4, 3, 2]),
    (.prism, ![0, 1, 4, 5, 3, 2]),
    (.prism, ![0, 1, 5, 4, 3, 2]),
    (.prism, ![0, 1, 4, 5, 2, 3]),
    (.prism, ![0, 1, 5, 4, 2, 3]),
    (.prism, ![0, 1, 2, 3, 5, 4]),
    (.prism, ![0, 1, 3, 2, 5, 4]),
    (.prism, ![0, 1, 2, 3, 4, 5]),
    (.prism, ![0, 1, 3, 2, 4, 5])]

theorem pairedGraphChoices_bijective : ∀ k, Function.Bijective (pairedGraphChoices k).2 := by decide

end SixVertexUnfolding.SmallGraphs
