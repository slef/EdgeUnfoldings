import SixVertexUnfolding.Geometry.PrismDiagonalFaces

/-! Identify the manuscript's sums of full face angles with the existing
geometric curvature. The two auxiliary diagonals split angles but are not cuts. -/

namespace SixVertexUnfolding.Prism

open FaceLabel

def quadFace : Fin 2 → FaceLabel := ![B, D]
def quadCorner : Fin 2 → Fin 4 → Fin 6 := ![![0, 3, 5, 2], ![2, 1, 4, 5]]

theorem sum_faces (f : FaceLabel → ℝ) :
    (∑ X, f X) = f A + f B + f C + f D + f E + f F := by
  rw [show (Finset.univ : Finset FaceLabel) = {A, B, C, D, E, F} by decide]
  simp
  ring

end SixVertexUnfolding.Prism

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Prism Prism.FaceLabel Real EuclideanGeometry

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
variable (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4)
variable (prism_kind : graph.kind = .prismDiagonal)

/-- The actual quadrilateral, in the order that uses the manuscript's auxiliary diagonal. -/
noncomputable def prismQuadrilateral (q : Fin 2) :
    (graph.prismDiagonalFace small_faces (quadFace q)).Quadrilateral := by
  let F := graph.prismDiagonalFace small_faces (quadFace q)
  let v : Fin 4 → P.Vertex := fun i => graph.prismVertex (quadCorner q i)
  have distinct : Function.Injective v := by
    intro i j same
    exact (by decide : ∀ q, Function.Injective (quadCorner q)) q
      (vertexLabel.injective (graph.vertex.injective same))
  have vertices : F.val ∩ (P.vertices : Set Space) = Set.range (fun i => (v i : Space)) := by
    rw [← F.image_vertexLabels graph.vertex]
    have labels : F.vertexLabels graph.vertex =
        Finset.univ.image (fun i => vertexLabel (quadCorner q i)) := by
      rw [graph.prismDiagonalFace_labels small_faces prism_kind]
      fin_cases q <;> decide
    rw [labels]
    ext x
    simp [v, prismVertex, Set.mem_range, Set.mem_image]
  have on_face (i : Fin 4) : (v i : Space) ∈ F.val := by
    have member : (v i : Space) ∈ F.val ∩ (P.vertices : Set Space) := by
      rw [vertices]
      exact ⟨i, rfl⟩
    exact member.1
  have four : (F.val ∩ (P.vertices : Set Space)).ncard = 4 := by
    rw [vertices, Set.ncard_range_of_injective (fun i j h => distinct (Subtype.ext h))]
    simp
  have nonedges := (by decide : ∀ q,
    ¬ SmallGraphs.SixGraphKind.prismDiagonal.adjacent
      (vertexLabel (quadCorner q 0)) (vertexLabel (quadCorner q 2)) ∧
    ¬ SmallGraphs.SixGraphKind.prismDiagonal.adjacent
      (vertexLabel (quadCorner q 1)) (vertexLabel (quadCorner q 3))) q
  exact {
    corner := v
    distinct := distinct
    vertices := vertices
    crossing := F.quadrilateral_crossing_of_nonedge four v distinct on_face
      (fun h => nonedges.1 (prism_kind ▸ (graph.edges _ _).mp h))
      (fun h => nonedges.2 (prism_kind ▸ (graph.edges _ _).mp h)) }

include prism_kind in
/-- Summing whole original-face corners gives exactly the subdivision's vertex angle sum. -/
theorem prismAngle_total (i : Fin 6) :
    (∑ f : FaceLabel, graph.prismAngle small_faces f i) = graph.totalAngleAt (vertexLabel i) := by
  have B0 := (graph.prismQuadrilateral small_faces prism_kind 0).angle_split 0
  have B5 := (graph.prismQuadrilateral small_faces prism_kind 0).angle_split 2
  have D2 := (graph.prismQuadrilateral small_faces prism_kind 1).angle_split 0
  have D4 := (graph.prismQuadrilateral small_faces prism_kind 1).angle_split 2
  change angle (graph.prismVertex 3 : Space) (graph.prismVertex 0) (graph.prismVertex 2) =
    angle (graph.prismVertex 3 : Space) (graph.prismVertex 0) (graph.prismVertex 5) +
    angle (graph.prismVertex 5 : Space) (graph.prismVertex 0) (graph.prismVertex 2) at B0
  change angle (graph.prismVertex 2 : Space) (graph.prismVertex 5) (graph.prismVertex 3) =
    angle (graph.prismVertex 2 : Space) (graph.prismVertex 5) (graph.prismVertex 0) +
    angle (graph.prismVertex 0 : Space) (graph.prismVertex 5) (graph.prismVertex 3) at B5
  change angle (graph.prismVertex 1 : Space) (graph.prismVertex 2) (graph.prismVertex 5) =
    angle (graph.prismVertex 1 : Space) (graph.prismVertex 2) (graph.prismVertex 4) +
    angle (graph.prismVertex 4 : Space) (graph.prismVertex 2) (graph.prismVertex 5) at D2
  change angle (graph.prismVertex 5 : Space) (graph.prismVertex 4) (graph.prismVertex 1) =
    angle (graph.prismVertex 5 : Space) (graph.prismVertex 4) (graph.prismVertex 2) +
    angle (graph.prismVertex 2 : Space) (graph.prismVertex 4) (graph.prismVertex 1) at D4
  simp [prismVertex, vertexLabel] at B0 B5 D2 D4
  fin_cases i <;>
    simp [sum_faces, graph.prismAngle_eq small_faces prism_kind, faceVertices, neighbors,
      prismVertex, vertexLabel, graph.totalAngleAt_eq_fan_angles,
      OctahedralTriangles.fanNeighbor, Fin.sum_univ_succ] <;>
    simp only [angle_comm] at * <;> linarith only [B0, B5, D2, D4]

include prism_kind in
/-- The curvature in the switching argument is the actual angular deficit of the solid. -/
theorem prism_curvature_eq (i : Fin 6) :
    graph.curvature (vertexLabel i) = 2 * π - ∑ f : FaceLabel, graph.prismAngle small_faces f i := by
  rw [graph.prismAngle_total small_faces prism_kind]
  rfl

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
