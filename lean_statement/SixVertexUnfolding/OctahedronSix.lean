import SixVertexUnfolding.Geometry.OctahedralSelectedLocal
import SixVertexUnfolding.OctahedronAngleCriteria
import SixVertexUnfolding.Geometry.OctahedralContactVisibility

/-! The selected development leaves precisely two opposite pairs and four remote pairs. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open OctahedralTriangles

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

/-- Six pairwise comparisons, all in this same selected development. -/
structure RemainingSix : Prop where
  opposite : net.OppositePetals
  remote : ∀ i : Fin 4, net.Separated (true, i) (false, i + 2)

/-- The local comparisons are proved from selection; these six comparisons complete the original-edge certificate. -/
theorem hasEdgeUnfolding_of_six_comparisons (octahedral : graph.kind = .octahedron)
    (source_order : graph.curvature (opposite source) ≤ graph.curvature source)
    (maximal : ∀ i, graph.curvature (fanNeighbor source i) ≤ graph.curvature (fanNeighbor source slit))
    (remaining : net.RemainingSix) : P.HasEdgeUnfolding := by
  have local_pairs := net.selected_local_pairs source_order maximal
  exact net.hasEdgeUnfolding_of_nine_comparisons octahedral {
    slit_petals := local_pairs.petals
    slit_left := local_pairs.left
    slit_right := local_pairs.right
    opposite_even := remaining.opposite.even
    opposite_odd := remaining.opposite.odd
    remote := remaining.remote
  }

/-- Outside the small-fan pocket branches, only the two remote finite-cut exclusions are still needed. -/
theorem hasEdgeUnfolding_of_selected_caseAB_and_cuts (octahedral : graph.kind = .octahedron)
    (source_order : graph.curvature (opposite source) ≤ graph.curvature source)
    (maximal : ∀ i, graph.curvature (fanNeighbor source i) ≤ graph.curvature (fanNeighbor source slit))
    (cases : ∀ i : Fin 2, net.widenedLeft i + net.widenedRight i < Real.pi ∨
      Real.pi ≤ net.leftFanCorner i + net.rightFanCorner i)
    (cuts : net.FiniteCutsClear) : P.HasEdgeUnfolding :=
  net.hasEdgeUnfolding_of_core octahedral (net.selected_local_pairs source_order maximal)
    (net.opposite_petals_of_paired_caseAB source_order cases) cuts

/-- At a high-curvature source, the first remote slit is proved clear; only the reflected slit remains outside the pocket branches. -/
theorem hasEdgeUnfolding_of_high_source_caseAB_and_second_cut (octahedral : graph.kind = .octahedron)
    (source_order : graph.curvature (opposite source) ≤ graph.curvature source)
    (source_high : Real.pi ≤ graph.curvature source)
    (maximal : ∀ i, graph.curvature (fanNeighbor source i) ≤ graph.curvature (fanNeighbor source slit))
    (cases : ∀ i : Fin 2, net.widenedLeft i + net.widenedRight i < Real.pi ∨
      Real.pi ≤ net.leftFanCorner i + net.rightFanCorner i)
    (second_cut : Disjoint (net.placedTriangle (true, 2))
      (segment ℝ 0 (graph.openingPoint (opposite source) slit 0))) : P.HasEdgeUnfolding := by
  apply net.hasEdgeUnfolding_of_selected_caseAB_and_cuts octahedral source_order maximal cases
  refine ⟨?_, second_cut⟩
  have first_cut := net.first_remote_cut_clear_of_high_source source_high
    (selected_slit_threshold (small_faces := small_faces) maximal).le
  simpa only [net.patch_right] using first_cut

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
