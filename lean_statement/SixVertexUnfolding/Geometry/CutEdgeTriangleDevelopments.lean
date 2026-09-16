import SixVertexUnfolding.Geometry.RadialStripDevelopments

/-! Every actual cut-tree edge has two compatible radial triangle
developments, with the fixed metric kite and the chosen shortest-route labels. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- Both sides of every cut-tree edge develop to their metric triangles, including original hinges. -/
theorem exists_cut_edge_triangle_developments (a : frontier P.body) (T : P.CutLocusTree a)
    {u v : T.vertices} (edge : T.graph.Adj u v) (S : CutEdgeStrips T edge) :
    ∃ M : CutEdgeMetricModel T edge, ∃ first second : C(unitInterval, P.BoundaryCurve),
      (∀ t, first (interiorTime t) = S.first t ∧ second (interiorTime t) = S.second t) ∧
      (∀ t, first t ∈ P.geodesicFiber a (T.closedEdgeTarget edge t) ∧
        second t ∈ P.geodesicFiber a (T.closedEdgeTarget edge t)) ∧
      Nonempty (RadialStripTriangle first M.first M.left M.right) ∧
      Nonempty (RadialStripTriangle second M.second M.left M.right) := by
  obtain ⟨first, second, agrees, member⟩ := graph.cut_edge_closed_routes small_faces a T edge S
  rcases T.open_edge_facet_type edge with ⟨F, contained, unique⟩ | ⟨F, G, shared, contained⟩
  · obtain ⟨p, _, q, _, different, terminal, profiles⟩ := graph.cut_edge_face_sources small_faces a T edge S F unique
    have base_length := P.faceCoordinates_rigid F u
      (by simpa only [T.closedEdgeTarget_zero] using contained 0) v
      (by simpa only [T.closedEdgeTarget_one] using contained 1)
    let M := CutEdgeMetricModel.fromAffineSources (P.faceCoordinates F) p q different base_length profiles
    refine ⟨M, first, second, agrees, member, ?_, ?_⟩
    · apply graph.face_strip_development small_faces a T edge first (fun t => (member t).1)
        F unique p (fun t => ?_) M.base_first_noncollinear
      rw [(agrees t).1]
      exact (terminal t).1
    · apply graph.face_strip_development small_faces a T edge second (fun t => (member t).2)
        F unique q (fun t => ?_) M.base_second_noncollinear
      rw [(agrees t).2]
      exact (terminal t).2
  · obtain ⟨center, inside⟩ := P.solid
    obtain ⟨facets⟩ := P.exists_normalized_facets inside
    obtain ⟨chart⟩ := exists_edge_folding facets F G shared
    have on_edge t := contained (interiorTime t)
    obtain ⟨p, _, q, _, different, terminal, profiles⟩ := chart.cut_edge_hinge_sources graph small_faces
      shared a T edge S on_edge
    have base_length := chart.left_rigid u
      (subset_affineSpan ℝ _ (by simpa only [T.closedEdgeTarget_zero] using (contained 0).1)) v
      (subset_affineSpan ℝ _ (by simpa only [T.closedEdgeTarget_one] using (contained 1).1))
    let M := CutEdgeMetricModel.fromAffineSources chart.left p q different base_length profiles
    refine ⟨M, first, second, agrees, member, ?_, ?_⟩
    · apply chart.hinge_strip_development graph small_faces shared a T edge first (fun t => (member t).1)
        on_edge p (fun t => ?_) M.base_first_noncollinear
      rw [(agrees t).1]
      exact (terminal t).1
    · apply chart.hinge_strip_development graph small_faces shared a T edge second (fun t => (member t).2)
        on_edge q (fun t => ?_) M.base_second_noncollinear
      rw [(agrees t).2]
      exact (terminal t).2

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
