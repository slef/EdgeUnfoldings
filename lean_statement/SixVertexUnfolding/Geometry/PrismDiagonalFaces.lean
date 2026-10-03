import SixVertexUnfolding.Geometry.OctahedralClosedLink
import SixVertexUnfolding.Geometry.FacetAngleSums

/-! The six original faces of the prism with a diagonal, in the manuscript's
labels A=021, B=0352, C=013, D=1254, E=143, F=345.
Every angle below is an angle of an actual whole original face. -/

namespace SixVertexUnfolding.Prism

inductive FaceLabel | A | B | C | D | E | F
  deriving DecidableEq, Fintype

open FaceLabel

/-- Convert the manuscript's vertex labels to the canonical graph labels. -/
def vertexLabel : Fin 6 ≃ Fin 6 where
  toFun := ![2, 0, 4, 5, 3, 1]
  invFun := ![1, 5, 0, 4, 2, 3]
  left_inv := by decide
  right_inv := by decide

def faceVertices : FaceLabel → Finset (Fin 6)
  | A => {0, 2, 1}
  | B => {0, 3, 5, 2}
  | C => {0, 1, 3}
  | D => {1, 2, 5, 4}
  | E => {1, 4, 3}
  | F => {3, 4, 5}

/-- One subdivision triangle identifies each whole original face. -/
def triangleIndex : FaceLabel → Fin 8
  | A => 0 | B => 4 | C => 1 | D => 2 | E => 3 | F => 7

/-- The two original edge neighbors at each face corner; absent corners are unused. -/
def neighbors : FaceLabel → Fin 6 → Fin 6 × Fin 6
  | A => ![(2, 1), (0, 2), (1, 0), (0, 0), (0, 0), (0, 0)]
  | B => ![(3, 2), (0, 0), (0, 5), (5, 0), (0, 0), (2, 3)]
  | C => ![(1, 3), (3, 0), (0, 0), (0, 1), (0, 0), (0, 0)]
  | D => ![(0, 0), (2, 4), (5, 1), (0, 0), (1, 5), (4, 2)]
  | E => ![(0, 0), (4, 3), (0, 0), (1, 4), (3, 1), (0, 0)]
  | F => ![(0, 0), (0, 0), (0, 0), (4, 5), (5, 3), (3, 4)]

end SixVertexUnfolding.Prism

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Prism Prism.FaceLabel Real EuclideanGeometry

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)

/-- A manuscript label denotes this genuine vertex of the solid. -/
noncomputable def prismVertex (i : Fin 6) : P.Vertex := graph.vertex (vertexLabel i)

theorem prismVertex_injective : Function.Injective (fun i => (graph.prismVertex i : Space)) := by
  intro i j same
  exact vertexLabel.injective (graph.vertex.injective (Subtype.ext same))

variable (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4)

noncomputable def prismDiagonalFace (f : FaceLabel) : P.Face :=
  graph.triangleFace small_faces (triangleIndex f)

/-- The full original-face angle, including both triangle pieces at a diagonal. -/
noncomputable def prismAngle (f : FaceLabel) (i : Fin 6) : ℝ :=
  (graph.prismDiagonalFace small_faces f).cornerAngle (graph.prismVertex i)

variable (prism_kind : graph.kind = .prismDiagonal)

include prism_kind

@[simp] theorem prismDiagonalFace_labels (f : FaceLabel) :
    (graph.prismDiagonalFace small_faces f).vertexLabels graph.vertex =
      (faceVertices f).image vertexLabel := by
  rw [prismDiagonalFace, graph.triangleFace_labels, prism_kind]
  cases f <;> decide

@[simp] theorem prismVertex_mem_face (f : FaceLabel) (i : Fin 6) :
    (graph.prismVertex i : Space) ∈ (graph.prismDiagonalFace small_faces f).val ↔
      i ∈ faceVertices f := by
  rw [prismVertex, ← Face.mem_vertexLabels, graph.prismDiagonalFace_labels small_faces prism_kind]
  simp only [Finset.mem_image, vertexLabel.injective.eq_iff, exists_eq_right]

/-- Compute a full face angle from its two original edge directions. -/
theorem prismAngle_eq (f : FaceLabel) (i : Fin 6) :
    graph.prismAngle small_faces f i = if i ∈ faceVertices f then
      angle (graph.prismVertex (neighbors f i).1 : Space) (graph.prismVertex i)
        (graph.prismVertex (neighbors f i).2) else 0 := by
  classical
  by_cases member : i ∈ faceVertices f
  · rw [if_pos member]
    have finite_data := (by decide : ∀ f i, i ∈ faceVertices f →
      (neighbors f i).1 ≠ (neighbors f i).2 ∧
      (neighbors f i).1 ∈ faceVertices f ∧ (neighbors f i).2 ∈ faceVertices f ∧
      SmallGraphs.SixGraphKind.prismDiagonal.adjacent (vertexLabel i) (vertexLabel (neighbors f i).1) ∧
      SmallGraphs.SixGraphKind.prismDiagonal.adjacent (vertexLabel i) (vertexLabel (neighbors f i).2)) f i member
    apply Face.cornerAngle_eq _ (small_faces _) _ _ _
    · exact graph.vertex.injective.ne (vertexLabel.injective.ne finite_data.1)
    · exact (graph.prismVertex_mem_face small_faces prism_kind f i).mpr member
    · exact (graph.prismVertex_mem_face small_faces prism_kind f _).mpr finite_data.2.1
    · exact (graph.prismVertex_mem_face small_faces prism_kind f _).mpr finite_data.2.2.1
    · exact (graph.edges _ _).mpr (prism_kind.symm ▸ finite_data.2.2.2.1)
    · exact (graph.edges _ _).mpr (prism_kind.symm ▸ finite_data.2.2.2.2)
  · rw [if_neg member]
    exact Face.cornerAngle_of_not_mem _ _
      (fun h => member ((graph.prismVertex_mem_face small_faces prism_kind f i).mp h))

/-- A vertex absent from an original face contributes zero to its angle sum. -/
theorem prismAngle_zero (f : FaceLabel) (i : Fin 6) (absent : i ∉ faceVertices f) :
    graph.prismAngle small_faces f i = 0 := by
  rw [graph.prismAngle_eq small_faces prism_kind, if_neg absent]

/-- All full original-face corners have strictly positive angle below π. -/
theorem prismAngle_bounds (f : FaceLabel) (i : Fin 6) (member : i ∈ faceVertices f) :
    0 < graph.prismAngle small_faces f i ∧ graph.prismAngle small_faces f i < π := by
  rw [graph.prismAngle_eq small_faces prism_kind, if_pos member]
  have distinct := (by decide : ∀ f i, i ∈ faceVertices f →
    (neighbors f i).1 ≠ i ∧ (neighbors f i).1 ≠ (neighbors f i).2 ∧ i ≠ (neighbors f i).2) f i member
  have noncollinear := P.no_three_collinear_vertices
    (graph.prismVertex (neighbors f i).1).property (graph.prismVertex i).property
    (graph.prismVertex (neighbors f i).2).property
    (graph.prismVertex_injective.ne distinct.1)
    (graph.prismVertex_injective.ne distinct.2.1)
    (graph.prismVertex_injective.ne distinct.2.2)
  exact ⟨angle_pos_of_not_collinear noncollinear, angle_lt_pi_of_not_collinear noncollinear⟩

/-- The strict link bound applies to the full face corner, not just a subdivision corner. -/
theorem prismAngle_link_bound (f : FaceLabel) (i : Fin 6) (member : i ∈ faceVertices f) :
    2 * graph.prismAngle small_faces f i < 2 * π - graph.curvature (vertexLabel i) := by
  rw [graph.prismAngle_eq small_faces prism_kind, if_pos member]
  have finite_data := (by decide : ∀ f i, i ∈ faceVertices f →
    vertexLabel (neighbors f i).1 ≠ vertexLabel i ∧
    vertexLabel (neighbors f i).2 ≠ vertexLabel i ∧
    vertexLabel (neighbors f i).1 ≠ OctahedralTriangles.opposite (vertexLabel i)) f i member
  exact graph.vertex_angle_lt_half_deficit small_faces _ _ _
    finite_data.1 finite_data.2.1 finite_data.2.2

/-- The original face sums are π for triangles and 2π for quadrilaterals. -/
theorem prismAngle_sum (f : FaceLabel) :
    (∑ i : Fin 6, graph.prismAngle small_faces f i) =
      (((faceVertices f).card - 2 : ℕ) : ℝ) * π := by
  have count := (graph.prismDiagonalFace small_faces f).vertexLabels_card graph.vertex
  rw [graph.prismDiagonalFace_labels small_faces prism_kind,
    Finset.card_image_of_injective _ vertexLabel.injective] at count
  calc
    _ = ∑ v : P.Vertex, (graph.prismDiagonalFace small_faces f).cornerAngle v :=
      (vertexLabel.trans graph.vertex).sum_comp _
    _ = _ := by rw [Face.sum_cornerAngles _ (small_faces _), ← count]

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
