import SixVertexUnfolding.Geometry.CutTreeConeBudget
import SixVertexUnfolding.Geometry.CutTreeConeCoverage

/-! The cumulative source-angle budget, now proved from the actual
surface geometry rather than assumed as cone-coverage data. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set Real

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4)
    {a : frontier P.body} (T : P.CutLocusTree a)
    [Fintype T.vertices] [DecidableRel T.graph.Adj]
    (models : (d : T.graph.Dart) → CutEdgeMetricModel T d.adj)

include small_faces in
/-- All directed source angles together are bounded by the source's actual cone angle. -/
theorem source_angle_sum_le (source : Fin 6)
    (at_source : (a : Space) = (graph.vertex source : Space)) :
    ∑ d, (models d).sourceAngle ≤ graph.totalAngleAt source :=
  graph.source_angle_sum_le_of_cone_coverage small_faces T models source at_source
    (graph.incident_model_angles_cover_cone small_faces a T models)

include small_faces in
/-- Counting each kite once gives a total source-angle budget strictly below π. -/
theorem half_source_angle_sum_lt_pi (source : Fin 6)
    (at_source : (a : Space) = (graph.vertex source : Space)) :
    (∑ d, (models d).sourceAngle) / 2 < π :=
  graph.half_source_angle_sum_lt_pi_of_cone_coverage small_faces T models source at_source
    (graph.incident_model_angles_cover_cone small_faces a T models)

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
