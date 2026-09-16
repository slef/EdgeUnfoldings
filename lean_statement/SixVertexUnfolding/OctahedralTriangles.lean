import SixVertexUnfolding.CanonicalSixFaces

/-! A common eight-triangle subdivision of the four canonical six-vertex surfaces. -/

namespace SixVertexUnfolding.OctahedralTriangles

open SmallGraphs

/-- The eight triangles choose one endpoint from each opposite pair 01, 23, 45. -/
def corner : Fin 8 → Fin 3 → Fin 6 :=
  ![![0, 2, 4], ![0, 2, 5], ![0, 3, 4], ![0, 3, 5],
    ![1, 2, 4], ![1, 2, 5], ![1, 3, 4], ![1, 3, 5]]

/-- The original labels belonging to a subdivision triangle. -/
def vertices (triangle : Fin 8) : Finset (Fin 6) :=
  Finset.univ.image (corner triangle)

/-- The whole original facet containing a subdivision triangle. -/
def carrier : SixGraphKind → Fin 8 → Finset (Fin 6)
  | .octahedron => ![{0, 2, 4}, {0, 2, 5}, {0, 3, 4}, {0, 3, 5},
      {1, 2, 4}, {1, 2, 5}, {1, 3, 4}, {1, 3, 5}]
  | .minusEdge => ![{0, 2, 4}, {0, 2, 5}, {0, 3, 4}, {0, 3, 5},
      {1, 2, 4, 5}, {1, 2, 4, 5}, {1, 3, 4}, {1, 3, 5}]
  | .prismDiagonal => ![{0, 2, 4}, {0, 2, 5}, {0, 1, 3, 4}, {0, 3, 5},
      {1, 2, 4, 5}, {1, 2, 4, 5}, {0, 1, 3, 4}, {1, 3, 5}]
  | .prism => ![{0, 2, 4}, {0, 2, 3, 5}, {0, 1, 3, 4}, {0, 2, 3, 5},
      {1, 2, 4, 5}, {1, 2, 4, 5}, {0, 1, 3, 4}, {1, 3, 5}]

/-- The three possible quadrilaterals, ordered to split along 12, 34, or 05 respectively. -/
def quadCorner : Fin 3 → Fin 4 → Fin 6 :=
  ![![1, 4, 2, 5], ![3, 0, 4, 1], ![0, 2, 5, 3]]

def quadVertices (q : Fin 3) : Finset (Fin 6) := Finset.univ.image (quadCorner q)

def quadPieces : Fin 3 → Fin 2 → Fin 8 := ![![4, 5], ![2, 6], ![1, 3]]

theorem corner_injective : ∀ triangle, Function.Injective (corner triangle) := by decide

theorem quadCorner_injective : ∀ q, Function.Injective (quadCorner q) := by decide

theorem carrier_mem_facets : ∀ kind triangle, carrier kind triangle ∈ kind.facets := by decide

theorem vertices_subset_carrier : ∀ kind triangle, vertices triangle ⊆ carrier kind triangle := by decide

/-- Every original facet is either an unchanged triangle or one of the three diagonal pairs. -/
theorem facet_cases : ∀ (kind : SixGraphKind) (face : Finset (Fin 6)), face ∈ kind.facets →
    (∃ triangle : Fin 8, carrier kind triangle = face ∧ vertices triangle = face) ∨
    (∃ q : Fin 3, quadVertices q = face ∧ ∀ piece, carrier kind (quadPieces q piece) = face) := by decide

/-- Both specified diagonals of each actual quadrilateral are nonedges of the original graph. -/
theorem quad_nonedge_diagonals : ∀ (kind : SixGraphKind) (q : Fin 3), quadVertices q ∈ kind.facets →
    ¬ kind.adjacent (quadCorner q 0) (quadCorner q 2) ∧
    ¬ kind.adjacent (quadCorner q 1) (quadCorner q 3) := by decide

/-- The two halves are exactly the corresponding subdivision triangles. -/
theorem quad_piece_vertices : ∀ q,
    vertices (quadPieces q 0) = {quadCorner q 0, quadCorner q 1, quadCorner q 2} ∧
    vertices (quadPieces q 1) = {quadCorner q 0, quadCorner q 2, quadCorner q 3} := by decide

end SixVertexUnfolding.OctahedralTriangles
