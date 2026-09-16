import SixVertexUnfolding.Geometry.OctahedralFanDevelopment
import SixVertexUnfolding.Geometry.OctahedralFanHinges
import SixVertexUnfolding.Geometry.QuadrilateralPlacementAgreement

/-! Consecutive fan triangles retain a single rigid placement when their radial hinge is a flat face diagonal. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.FanDevelopment

open OctahedralTriangles

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {pole : Fin 6} {slit : Fin 4}
variable (fan : graph.FanDevelopment small_faces pole slit)

private theorem cofacial_fan_data : ∀ (kind : SmallGraphs.SixGraphKind) (p : Fin 6) (j : Fin 4),
    carrier kind (fanTriangle p j) = carrier kind (fanTriangle p (j + 1)) →
      (carrier kind (fanTriangle p j)).card = 4 ∧ ¬ kind.adjacent p (fanNeighbor p (j + 1)) := by decide

/-- A flat radial hinge joins both subdivision pieces as one original facet. -/
theorem flat_fan_agreement (i : Fin 3)
    (same : graph.triangleFace small_faces (fanTriangle pole (slit + i.castSucc)) =
      graph.triangleFace small_faces (fanTriangle pole (slit + i.succ))) :
    Set.EqOn (fan.place i.castSucc) (fan.place i.succ)
      (graph.triangleFace small_faces (fanTriangle pole (slit + i.castSucc))).val := by
  let j := slit + i.castSucc
  let F := graph.triangleFace small_faces (fanTriangle pole j)
  have next : j + 1 = slit + i.succ := by
    dsimp [j]
    rw [add_assoc]
    congr 1
    exact (by decide : ∀ i : Fin 3, (i.castSucc : Fin 4) + 1 = i.succ) i
  have labels : carrier graph.kind (fanTriangle pole j) = carrier graph.kind (fanTriangle pole (j + 1)) := by
    have identity := congrArg (fun G : P.Face => G.vertexLabels graph.vertex) same
    simpa only [graph.triangleFace_labels, next, j] using identity
  have data := cofacial_fan_data graph.kind pole j labels
  have four : (F.val ∩ (P.vertices : Set Space)).ncard = 4 := by
    rw [← Face.vertexLabels_card graph.vertex F]
    dsimp only [F]
    rw [graph.triangleFace_labels]
    exact data.1
  let labels4 : Fin 4 → Fin 6 := ![pole, fanNeighbor pole j, fanNeighbor pole (j + 1), fanNeighbor pole ((j + 1) + 1)]
  let v : Fin 4 → P.Vertex := fun k => graph.vertex (labels4 k)
  have distinct : Function.Injective v := graph.vertex.injective.comp
    ((by decide : ∀ p j, Function.Injective (![p, fanNeighbor p j, fanNeighbor p (j + 1),
      fanNeighbor p ((j + 1) + 1)] : Fin 4 → Fin 6)) pole j)
  have aF : (v 0 : Space) ∈ F.val := graph.fan_sector_on_face pole small_faces j _ (by simp [labels4])
  have bF : (v 2 : Space) ∈ F.val := graph.fan_sector_on_face pole small_faces j _ (by simp [labels4])
  have cF : (v 1 : Space) ∈ F.val := graph.fan_sector_on_face pole small_faces j _ (by simp [labels4])
  have dF : (v 3 : Space) ∈ F.val := by
    change _ ∈ (graph.triangleFace small_faces (fanTriangle pole (slit + i.castSucc))).val
    rw [same]
    exact graph.fan_sector_on_face pole small_faces (slit + i.succ) _ (by simp [labels4, next])
  obtain ⟨q, hinge, crossing⟩ := F.quadrilateral_crossing_of_nonedge four v distinct
    (fun k => by fin_cases k; exacts [aF, cF, bF, dF])
    (fun edge => data.2 ((graph.edges _ _).mp edge))
    (fun edge => (by decide : ∀ (kind : SmallGraphs.SixGraphKind) (p : Fin 6) (j : Fin 4),
      ¬ kind.adjacent (fanNeighbor p j) (fanNeighbor p ((j + 1) + 1))) graph.kind pole j ((graph.edges _ _).mp edge))
  apply F.placements_agree_across_diagonal (v 0) (v 2) (v 1) (v 3)
    (distinct.ne (by decide)) (distinct.ne (by decide)) (distinct.ne (by decide))
    (distinct.ne (by decide)) (distinct.ne (by decide)) aF bF cF dF
    ⟨q, openSegment_subset_segment ℝ _ _ hinge, crossing⟩ (fan.place i.castSucc) (fan.place i.succ) (fan.rigid i.castSucc)
  · dsimp only [F, j]
    rw [same]
    exact fan.rigid i.succ
  · exact (fan.at_pole i.castSucc).trans (fan.at_pole i.succ).symm
  · exact fan.joined i _ (right_mem_segment ℝ _ _)
  · change OppositeHingeSides (fan.place i.castSucc (graph.vertex pole))
      (fan.place i.castSucc (graph.vertex (fanNeighbor pole (j + 1))))
      (fan.place i.castSucc (graph.vertex (fanNeighbor pole j)))
      (fan.place i.succ (graph.vertex (fanNeighbor pole ((j + 1) + 1))))
    rw [fan.at_pole, show j = slit + i.castSucc from rfl, fan.at_right, fan.at_left]
    rw [← show j = slit + i.castSucc from rfl, next, fan.at_right]
    exact graph.opening_hinge_outward pole slit i

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.FanDevelopment
