import SixVertexUnfolding.OctahedronSix
import SixVertexUnfolding.Geometry.OctahedralSecondContactVisibility

/-! Both remote finite-cut exclusions are proved when the source curvature is at least pi. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open Real OctahedralTriangles

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

/-- Closed boundary contact is excluded at both remote petals, including all slit and petal endpoints. -/
theorem high_source_finite_cuts_clear (source_high : π ≤ graph.curvature source)
    (threshold : π ≤ 2 * graph.curvature (fanNeighbor source slit) + graph.curvature (opposite source)) :
    net.FiniteCutsClear := by
  refine ⟨?_, ?_⟩
  · simpa only [net.patch_right] using net.first_remote_cut_clear_of_high_source source_high threshold
  · simpa only [net.patch_left] using net.second_remote_cut_clear_of_high_source source_high threshold

/-- No cut-clearance or pair-separation premise remains in this selected high-source Cases A/B region. -/
theorem hasEdgeUnfolding_of_high_source_and_caseAB (octahedral : graph.kind = .octahedron)
    (source_order : graph.curvature (opposite source) ≤ graph.curvature source)
    (source_high : π ≤ graph.curvature source)
    (maximal : ∀ i, graph.curvature (fanNeighbor source i) ≤ graph.curvature (fanNeighbor source slit))
    (cases : ∀ i : Fin 2, net.widenedLeft i + net.widenedRight i < π ∨
      π ≤ net.leftFanCorner i + net.rightFanCorner i) : P.HasEdgeUnfolding :=
  net.hasEdgeUnfolding_of_selected_caseAB_and_cuts octahedral source_order maximal cases
    (net.high_source_finite_cuts_clear source_high (selected_slit_threshold (small_faces := small_faces) maximal).le)

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
