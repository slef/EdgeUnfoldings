import SixVertexUnfolding.Geometry.OctahedralLocalBoundary
import SixVertexUnfolding.Geometry.OctahedralSelection

/-! The paired-pole and maximum-slit choices discharge every hypothesis of the local lemma. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open Real OctahedralTriangles

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

include small_faces in
theorem selected_slit_threshold
    (maximal : ∀ i, graph.curvature (fanNeighbor source i) ≤ graph.curvature (fanNeighbor source slit)) :
    π < 2 * graph.curvature (fanNeighbor source slit) + graph.curvature (opposite source) :=
  Curvature.equator_maximum_slit_threshold (graph.curvature_poles_equator source)
    (graph.curvature_lt_two_pi source) (graph.curvature_pos small_faces _) maximal

/-- No local angle or nonoverlap assumption remains for the selected source and slit. -/
theorem selected_local_pairs
    (source_order : graph.curvature (opposite source) ≤ graph.curvature source)
    (maximal : ∀ i, graph.curvature (fanNeighbor source i) ≤ graph.curvature (fanNeighbor source slit)) : net.LocalPairs :=
  net.local_pairs (Curvature.half_fan_alternative source_order) (selected_slit_threshold (small_faces := small_faces) maximal).le

theorem selected_local_flank_cuts
    (source_order : graph.curvature (opposite source) ≤ graph.curvature source)
    (maximal : ∀ i, graph.curvature (fanNeighbor source i) ≤ graph.curvature (fanNeighbor source slit)) :
    Disjoint (net.placedTriangle (true, 0)) (segment ℝ 0 (net.patch 3).right) ∧
      Disjoint (net.placedTriangle (true, 3)) (segment ℝ 0 (net.patch 0).left) :=
  net.local_flank_cuts (Curvature.half_fan_alternative source_order) (selected_slit_threshold (small_faces := small_faces) maximal).le

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
