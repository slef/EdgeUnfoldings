import SixVertexUnfolding.OctahedronHighSource
import SixVertexUnfolding.Geometry.OctahedralFiniteContact

/-! After the complete local and finite-contact arguments, only two opposite-petal comparisons remain. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open Real OctahedralTriangles

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

/-- The two opposite-petal comparisons complete the selected original-edge octahedron certificate. -/
theorem hasEdgeUnfolding_of_two_comparisons (octahedral : graph.kind = .octahedron)
    (source_order : graph.curvature (opposite source) ≤ graph.curvature source)
    (maximal : ∀ i, graph.curvature (fanNeighbor source i) ≤ graph.curvature (fanNeighbor source slit))
    (opposite_pairs : net.OppositePetals) : P.HasEdgeUnfolding :=
  net.hasEdgeUnfolding_of_core octahedral (net.selected_local_pairs source_order maximal)
    opposite_pairs (net.selected_finite_cuts_clear source_order maximal)

/-- Outside the small-fan pocket branches, the selected octahedral development is fully proved nonoverlapping. -/
theorem hasEdgeUnfolding_of_selected_caseAB (octahedral : graph.kind = .octahedron)
    (source_order : graph.curvature (opposite source) ≤ graph.curvature source)
    (maximal : ∀ i, graph.curvature (fanNeighbor source i) ≤ graph.curvature (fanNeighbor source slit))
    (cases : ∀ i : Fin 2, net.widenedLeft i + net.widenedRight i < π ∨
      π ≤ net.leftFanCorner i + net.rightFanCorner i) : P.HasEdgeUnfolding :=
  net.hasEdgeUnfolding_of_two_comparisons octahedral source_order maximal
    (net.opposite_petals_of_paired_caseAB source_order cases)

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
