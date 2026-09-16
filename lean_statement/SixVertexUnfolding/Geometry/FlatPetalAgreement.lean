import SixVertexUnfolding.Geometry.OctahedralNetPlacement
import SixVertexUnfolding.Geometry.QuadrilateralPlacementAgreement

/-! When a fan triangle and its petal belong to one quadrilateral, their affine placements agree on that whole face. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open OctahedralTriangles OctahedralNet

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

private theorem cofacial_petal_data : ∀ (kind : SmallGraphs.SixGraphKind) (s : Fin 6) (j : Fin 4),
    carrier kind (fanTriangle (opposite s) j) = carrier kind (fanTriangle s j) →
      (carrier kind (fanTriangle (opposite s) j)).card = 4 ∧
        ¬ kind.adjacent (fanNeighbor s j) (fanNeighbor s (j + 1)) := by decide

/-- The flat equator hinge retains the original quadrilateral as one rigid face. -/
theorem flat_petal_agreement (i : Fin 4)
    (same : graph.netFace small_faces source slit (false, i) = graph.netFace small_faces source slit (true, i)) :
    Set.EqOn (net.fan.place i) (net.petal i) (graph.netFace small_faces source slit (false, i)).val := by
  let F := graph.triangleFace small_faces (fanTriangle (opposite source) (slit + i))
  change F = graph.triangleFace small_faces (fanTriangle source (slit + i)) at same
  have labels : carrier graph.kind (fanTriangle (opposite source) (slit + i)) =
      carrier graph.kind (fanTriangle source (slit + i)) := by
    have identity := congrArg (fun G : P.Face => G.vertexLabels graph.vertex) same
    simpa only [F, graph.triangleFace_labels] using identity
  have data := cofacial_petal_data graph.kind source (slit + i) labels
  have four : (F.val ∩ (P.vertices : Set Space)).ncard = 4 := by
    rw [← Face.vertexLabels_card graph.vertex F]
    dsimp only [F]
    rw [graph.triangleFace_labels]
    exact data.1
  let labels4 : Fin 4 → Fin 6 := ![fanNeighbor source (slit + i), opposite source,
    fanNeighbor source ((slit + i) + 1), source]
  let v : Fin 4 → P.Vertex := fun j => graph.vertex (labels4 j)
  have distinct : Function.Injective v := graph.vertex.injective.comp
    ((by decide : ∀ s j, Function.Injective (![fanNeighbor s j, opposite s, fanNeighbor s (j + 1), s] : Fin 4 → Fin 6)) source (slit + i))
  have paired : ∀ s j, fanNeighbor (opposite s) j = fanNeighbor s j := by decide
  have aF : (v 0 : Space) ∈ F.val := graph.fan_sector_on_face (opposite source) small_faces (slit + i) _ (by simp [labels4, paired])
  have bF : (v 2 : Space) ∈ F.val := graph.fan_sector_on_face (opposite source) small_faces (slit + i) _ (by simp [labels4, paired])
  have cF : (v 1 : Space) ∈ F.val := graph.fan_sector_on_face (opposite source) small_faces (slit + i) _ (by simp [labels4])
  have dF : (v 3 : Space) ∈ F.val := by
    rw [same]
    exact graph.fan_sector_on_face source small_faces (slit + i) _ (by simp [labels4])
  obtain ⟨q, hinge, crossing⟩ := F.quadrilateral_crossing_of_nonedge four v distinct
    (fun j => by fin_cases j; exacts [aF, cF, bF, dF])
    (fun edge => data.2 ((graph.edges _ _).mp edge))
    (fun edge => (by decide : ∀ (kind : SmallGraphs.SixGraphKind) (s : Fin 6),
      ¬ kind.adjacent (opposite s) s) graph.kind source ((graph.edges _ _).mp edge))
  have left_position : net.fan.place i (v 0) = (net.patch i).left := by
    change net.fan.place i (graph.vertex (fanNeighbor source (slit + i))) = _
    rw [← paired source (slit + i), net.fan.at_left, net.patch_left]
  have right_position : net.fan.place i (v 2) = (net.patch i).right := by
    change net.fan.place i (graph.vertex (fanNeighbor source ((slit + i) + 1))) = _
    rw [← paired source ((slit + i) + 1), net.fan.at_right, net.patch_right]
  apply F.placements_agree_across_diagonal (v 0) (v 2) (v 1) (v 3)
    (distinct.ne (by decide)) (distinct.ne (by decide)) (distinct.ne (by decide))
    (distinct.ne (by decide)) (distinct.ne (by decide)) aF bF cF dF
    ⟨q, openSegment_subset_segment ℝ _ _ hinge, crossing⟩ (net.fan.place i) (net.petal i) (net.fan.rigid i)
  · rw [same]
    exact net.petal_rigid i
  · rw [left_position]
    exact (net.petal_left i).symm
  · rw [right_position]
    exact (net.petal_right i).symm
  · rw [left_position, right_position]
    change OppositeHingeSides _ _ (net.fan.place i (graph.vertex (opposite source))) (net.petal i (graph.vertex source))
    rw [net.fan.at_pole, net.petal_apex, ← net.patch_pole i]
    exact (net.patch i).outward

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
