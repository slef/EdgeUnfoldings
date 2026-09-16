import SixVertexUnfolding.Geometry.CutEdgeTriangleDevelopments
import SixVertexUnfolding.Geometry.SmallPolyhedronClosedCutEdgeRoutes
import SixVertexUnfolding.Geometry.SmallPolyhedronCutEdgeFaceSources
import SixVertexUnfolding.Geometry.SmallPolyhedronCutEdgeHingeSources
import SixVertexUnfolding.Geometry.SmallPolyhedronRadialStripDevelopments

/-! Every actual cut-tree edge has two compatible radial triangle
developments, with the fixed metric kite and the chosen shortest-route labels.

Here the shortest-route inputs come from the actual vertex fans of a
polyhedron with at most six vertices and triangular/quadrilateral faces.
No canonical graph model is assumed. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

variable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include size small_faces in
/-- Both sides of every cut-tree edge develop to their metric triangles, including original hinges. -/
theorem small_exists_cut_edge_triangle_developments (a : frontier P.body) (T : P.CutLocusTree a)
    {u v : T.vertices} (edge : T.graph.Adj u v) (S : CutEdgeStrips T edge) :
    ∃ M : CutEdgeMetricModel T edge, ∃ first second : C(unitInterval, P.BoundaryCurve),
      (∀ t, first (interiorTime t) = S.first t ∧ second (interiorTime t) = S.second t) ∧
      (∀ t, first t ∈ P.geodesicFiber a (T.closedEdgeTarget edge t) ∧
        second t ∈ P.geodesicFiber a (T.closedEdgeTarget edge t)) ∧
      Nonempty (RadialStripTriangle first M.first M.left M.right) ∧
      Nonempty (RadialStripTriangle second M.second M.left M.right) := by
  obtain ⟨first, second, agrees, member⟩ := small_cut_edge_closed_routes size small_faces a T edge S
  rcases T.open_edge_facet_type edge with ⟨F, contained, unique⟩ | ⟨F, G, shared, contained⟩
  · obtain ⟨p, _, q, _, different, terminal, profiles⟩ := small_cut_edge_face_sources size small_faces a T edge S F unique
    have base_length := P.faceCoordinates_rigid F u
      (by simpa only [T.closedEdgeTarget_zero] using contained 0) v
      (by simpa only [T.closedEdgeTarget_one] using contained 1)
    let M := CutEdgeMetricModel.fromAffineSources (P.faceCoordinates F) p q different base_length profiles
    refine ⟨M, first, second, agrees, member, ?_, ?_⟩
    · apply small_face_strip_development size small_faces a T edge first (fun t => (member t).1)
        F unique p (fun t => ?_) M.base_first_noncollinear
      rw [(agrees t).1]
      exact (terminal t).1
    · apply small_face_strip_development size small_faces a T edge second (fun t => (member t).2)
        F unique q (fun t => ?_) M.base_second_noncollinear
      rw [(agrees t).2]
      exact (terminal t).2
  · obtain ⟨center, inside⟩ := P.solid
    obtain ⟨facets⟩ := P.exists_normalized_facets inside
    obtain ⟨chart⟩ := exists_edge_folding facets F G shared
    have on_edge t := contained (interiorTime t)
    obtain ⟨p, _, q, _, different, terminal, profiles⟩ := chart.small_cut_edge_hinge_sources size small_faces
      shared a T edge S on_edge
    have base_length := chart.left_rigid u
      (subset_affineSpan ℝ _ (by simpa only [T.closedEdgeTarget_zero] using (contained 0).1)) v
      (subset_affineSpan ℝ _ (by simpa only [T.closedEdgeTarget_one] using (contained 1).1))
    let M := CutEdgeMetricModel.fromAffineSources chart.left p q different base_length profiles
    refine ⟨M, first, second, agrees, member, ?_, ?_⟩
    · apply chart.small_hinge_strip_development size small_faces shared a T edge first (fun t => (member t).1)
        on_edge p (fun t => ?_) M.base_first_noncollinear
      rw [(agrees t).1]
      exact (terminal t).1
    · apply chart.small_hinge_strip_development size small_faces shared a T edge second (fun t => (member t).2)
        on_edge q (fun t => ?_) M.base_second_noncollinear
      rw [(agrees t).2]
      exact (terminal t).2

end SixVertexUnfolding.ConvexPolyhedron
