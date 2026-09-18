import SixVertexUnfolding.Geometry.SubdivisionCertificate
import SixVertexUnfolding.Geometry.FlatPetalAgreement

/-! The octahedron-minus-edge case keeps its sole quadrilateral diagonal uncut by choosing poles 4 and 5. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open OctahedralTriangles OctahedralNet

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- With these poles, the only repeated carrier is one attached fan-petal pair. -/
theorem minusEdge_cofacial_indices : ∀ (source : Fin 6), source = 4 ∨ source = 5 →
    ∀ (slit : Fin 4) (x y : FaceIndex),
      carrier .minusEdge (OctahedralNet.triangle source slit x) = carrier .minusEdge (OctahedralNet.triangle source slit y) →
        x = y ∨ (∃ i : Fin 4, x = (false, i) ∧ y = (true, i)) ∨
          (∃ i : Fin 4, x = (true, i) ∧ y = (false, i)) := by decide

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}

/-- The two pieces of the quadrilateral use the same placement on the whole original face. -/
theorem Development.minusEdge_consistent (net : graph.Development small_faces source slit)
    (kind : graph.kind = .minusEdge) (poles : source = 4 ∨ source = 5)
    (x y : FaceIndex) (same : graph.netFace small_faces source slit x = graph.netFace small_faces source slit y) :
    Set.EqOn (net.place x) (net.place y) (graph.netFace small_faces source slit y).val := by
  have labels := congrArg (fun F : P.Face => F.vertexLabels graph.vertex) same
  change (graph.triangleFace small_faces _).vertexLabels graph.vertex =
    (graph.triangleFace small_faces _).vertexLabels graph.vertex at labels
  rw [graph.triangleFace_labels, graph.triangleFace_labels, kind] at labels
  rcases minusEdge_cofacial_indices source poles slit x y labels with rfl | ⟨i, rfl, rfl⟩ | ⟨i, rfl, rfl⟩
  · exact fun _ _ => rfl
  · rw [← same]
    exact net.flat_petal_agreement i same
  · exact (net.flat_petal_agreement i same.symm).symm

/-- Every convex solid with this original graph has an original-edge unfolding with its quadrilateral kept whole. -/
theorem hasEdgeUnfolding_of_minusEdge (graph : P.SixVertexGraph)
    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4)
    (kind : graph.kind = .minusEdge) : P.HasEdgeUnfolding := by
  obtain ⟨source, endpoints, source_order⟩ := graph.exists_sharper_pole 4
  have poles : source = 4 ∨ source = 5 := by
    simpa only [show opposite 4 = 5 from rfl] using endpoints
  obtain ⟨slit, maximal, _, _⟩ := graph.exists_curvature_slit small_faces source
  obtain ⟨net⟩ := graph.exists_development small_faces source slit
  exact net.hasEdgeUnfolding_of_consistent_subdivision source_order maximal (net.minusEdge_consistent kind poles)

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
