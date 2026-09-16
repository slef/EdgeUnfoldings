import SixVertexUnfolding.Geometry.SubdivisionCertificate
import SixVertexUnfolding.Geometry.FlatPetalAgreement
import SixVertexUnfolding.Geometry.FlatFanAgreement

/-! The common selected development unfolds whole facets whenever its five cut edges are original edges. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open OctahedralTriangles OctahedralNet

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- If all cuts are original, two different pieces of one facet are joined by a retained flat hinge. -/
theorem cofacial_indices_of_original_cuts : ∀ (kind : SmallGraphs.SixGraphKind) (source : Fin 6) (slit : Fin 4),
    (∀ j : Fin 4, kind.adjacent source (fanNeighbor source j)) →
    kind.adjacent (opposite source) (fanNeighbor source slit) →
    ∀ x y : FaceIndex, carrier kind (OctahedralNet.triangle source slit x) =
      carrier kind (OctahedralNet.triangle source slit y) → x = y ∨ hinges.Adj x y := by
  intro kind source slit
  change (∀ j : Fin 4, kind.adjacent source (fanNeighbor source j)) →
    kind.adjacent (opposite source) (fanNeighbor source slit) →
    ∀ x y : FaceIndex, carrier kind (OctahedralNet.triangle source slit x) =
      carrier kind (OctahedralNet.triangle source slit y) → x = y ∨
      (x.1 = false ∧ y.1 = false ∧ (x.2.val + 1 = y.2.val ∨ y.2.val + 1 = x.2.val) ∨
        x.1 ≠ y.1 ∧ x.2 = y.2)
  revert kind source slit
  decide

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}

namespace Development

variable (net : graph.Development small_faces source slit)

/-- Every retained flat hinge gives agreement on the whole original carrier facet. -/
theorem flat_hinge_agreement (x y : FaceIndex) (edge : hinges.Adj x y)
    (same : graph.netFace small_faces source slit x = graph.netFace small_faces source slit y) :
    Set.EqOn (net.place x) (net.place y) (graph.netFace small_faces source slit y).val := by
  rcases hinge_cases x y edge with ⟨i, rfl, rfl⟩ | ⟨i, rfl, rfl⟩ | ⟨i, rfl, rfl⟩ | ⟨i, rfl, rfl⟩
  · rw [← same]
    exact net.fan.flat_fan_agreement i same
  · exact (net.fan.flat_fan_agreement i same.symm).symm
  · rw [← same]
    exact net.flat_petal_agreement i same
  · exact (net.flat_petal_agreement i same.symm).symm

include net in
/-- Original cuts plus the proved curvature selection give a complete whole-face unfolding. -/
theorem hasEdgeUnfolding_of_original_selected_cuts
    (source_order : graph.curvature (opposite source) ≤ graph.curvature source)
    (maximal : ∀ i, graph.curvature (fanNeighbor source i) ≤ graph.curvature (fanNeighbor source slit))
    (source_edges : ∀ j : Fin 4, P.edgeGraph.Adj (graph.vertex source) (graph.vertex (fanNeighbor source j)))
    (slit_edge : P.edgeGraph.Adj (graph.vertex (opposite source)) (graph.vertex (fanNeighbor source slit))) :
    P.HasEdgeUnfolding := by
  apply net.hasEdgeUnfolding_of_consistent_subdivision source_order maximal
  intro x y same
  have labels := congrArg (fun F : P.Face => F.vertexLabels graph.vertex) same
  change (graph.triangleFace small_faces _).vertexLabels graph.vertex =
    (graph.triangleFace small_faces _).vertexLabels graph.vertex at labels
  rw [graph.triangleFace_labels, graph.triangleFace_labels] at labels
  rcases cofacial_indices_of_original_cuts graph.kind source slit
    (fun j => (graph.edges _ _).mp (source_edges j)) ((graph.edges _ _).mp slit_edge) x y labels with rfl | edge
  · exact fun _ _ => rfl
  · exact net.flat_hinge_agreement x y edge same

end Development

/-- An eligible source and a largest-curvature original slit are sufficient; all planar choices are constructed. -/
theorem hasEdgeUnfolding_of_original_cut_selection (graph : P.SixVertexGraph)
    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4)
    (source : Fin 6) (slit : Fin 4)
    (source_order : graph.curvature (opposite source) ≤ graph.curvature source)
    (maximal : ∀ i, graph.curvature (fanNeighbor source i) ≤ graph.curvature (fanNeighbor source slit))
    (source_edges : ∀ j : Fin 4, P.edgeGraph.Adj (graph.vertex source) (graph.vertex (fanNeighbor source j)))
    (slit_edge : P.edgeGraph.Adj (graph.vertex (opposite source)) (graph.vertex (fanNeighbor source slit))) :
    P.HasEdgeUnfolding := by
  obtain ⟨net⟩ := graph.exists_development small_faces source slit
  exact net.hasEdgeUnfolding_of_original_selected_cuts source_order maximal source_edges slit_edge

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
