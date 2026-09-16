import SixVertexUnfolding.OctahedralTriangles

/-! The four incident subdivision triangles at each of the six original vertices. -/

namespace SixVertexUnfolding.OctahedralTriangles

/-- The opposite endpoint in the three fixed nonedge pairs. -/
def opposite : Fin 6 → Fin 6 := ![1, 0, 3, 2, 5, 4]

/-- The other four vertices in their cyclic order around a source vertex. -/
def fanNeighbor : Fin 6 → Fin 4 → Fin 6 :=
  ![![2, 4, 3, 5], ![2, 4, 3, 5], ![0, 4, 1, 5],
    ![0, 4, 1, 5], ![0, 2, 1, 3], ![0, 2, 1, 3]]

/-- The corresponding four subdivision triangles, in the same cyclic order. -/
def fanTriangle : Fin 6 → Fin 4 → Fin 8 :=
  ![![0, 2, 3, 1], ![4, 6, 7, 5], ![0, 4, 5, 1],
    ![2, 6, 7, 3], ![0, 4, 6, 2], ![1, 5, 7, 3]]

theorem fanNeighbor_injective : ∀ v, Function.Injective (fanNeighbor v) := by decide

theorem fanNeighbor_ne_source : ∀ v i, fanNeighbor v i ≠ v := by decide

theorem fanNeighbor_exhaust : ∀ v w, w ≠ v → w ≠ opposite v → ∃ i, fanNeighbor v i = w := by decide

theorem opposite_nonedge : ∀ (kind : SmallGraphs.SixGraphKind) v,
    ¬ kind.adjacent v (opposite v) := by decide

theorem opposite_ne : ∀ v, opposite v ≠ v := by decide

theorem opposite_opposite : ∀ v, opposite (opposite v) = v := by decide

/-- A subdivision triangle never contains both ends of an opposite pair. -/
theorem corner_ne_opposite : ∀ t i j, corner t i ≠ opposite (corner t j) := by decide

/-- The poles and cyclic equator count each of the six vertices once. -/
theorem sum_poles_equator (quantity : Fin 6 → ℝ) (v : Fin 6) :
    quantity v + quantity (opposite v) + (∑ i : Fin 4, quantity (fanNeighbor v i)) =
      ∑ w : Fin 6, quantity w := by
  fin_cases v <;> simp [opposite, fanNeighbor, Fin.sum_univ_succ] <;> ring

/-- Each fan sector has precisely the source and the two successive neighboring rays. -/
theorem fanTriangle_vertices : ∀ v i,
    vertices (fanTriangle v i) = {v, fanNeighbor v i, fanNeighbor v (i + 1)} := by decide

end SixVertexUnfolding.OctahedralTriangles
