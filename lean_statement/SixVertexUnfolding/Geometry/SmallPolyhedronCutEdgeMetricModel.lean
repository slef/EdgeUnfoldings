import SixVertexUnfolding.Geometry.CutEdgeMetricModel
import SixVertexUnfolding.Geometry.SmallPolyhedronCutEdgeFaceSources
import SixVertexUnfolding.Geometry.SmallPolyhedronCutEdgeHingeSources
import SixVertexUnfolding.Geometry.SmallPolyhedronCutEdgeStrips

/-! Every cut-tree edge has a pair of planar metric triangles. Their
base length and all radial lengths are proved from the actual surface.
Identification of the full strips with these triangles is a further step.

Here the shortest-route inputs come from the actual vertex fans of a
polyhedron with at most six vertices and triangular/quadrilateral faces.
No canonical graph model is assumed. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

variable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include size small_faces in
/-- Every actual cut-tree edge has its two metric triangles, including edges along original hinges. -/
theorem small_exists_cut_edge_metric_model (a : frontier P.body) (T : P.CutLocusTree a)
    {u v : T.vertices} (edge : T.graph.Adj u v) : Nonempty (CutEdgeMetricModel T edge) := by
  obtain ⟨S⟩ := small_exists_cut_edge_strips size small_faces a T edge
  rcases T.open_edge_facet_type edge with ⟨F, contained, unique⟩ | ⟨F, G, shared, contained⟩
  · obtain ⟨p, _, q, _, different, _, profiles⟩ := small_cut_edge_face_sources size small_faces a T edge S F unique
    apply CutEdgeMetricModel.of_affine_sources (P.faceCoordinates F) p q different ?_ profiles
    exact P.faceCoordinates_rigid F u (by simpa only [T.closedEdgeTarget_zero] using contained 0)
      v (by simpa only [T.closedEdgeTarget_one] using contained 1)
  · obtain ⟨center, inside⟩ := P.solid
    obtain ⟨facets⟩ := P.exists_normalized_facets inside
    obtain ⟨chart⟩ := exists_edge_folding facets F G shared
    obtain ⟨p, _, q, _, different, _, profiles⟩ := chart.small_cut_edge_hinge_sources size small_faces shared a T edge S
      (fun t => contained (interiorTime t))
    apply CutEdgeMetricModel.of_affine_sources chart.left p q different ?_ profiles
    exact chart.left_rigid u (subset_affineSpan ℝ _ (by simpa only [T.closedEdgeTarget_zero] using (contained 0).1))
      v (subset_affineSpan ℝ _ (by simpa only [T.closedEdgeTarget_one] using (contained 1).1))

end SixVertexUnfolding.ConvexPolyhedron
