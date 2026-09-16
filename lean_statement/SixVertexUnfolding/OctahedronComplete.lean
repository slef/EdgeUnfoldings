import SixVertexUnfolding.OctahedronTwo
import SixVertexUnfolding.Geometry.OctahedralPocketContradiction

/-! Every convex octahedron has an original-edge unfolding: all three opposite-petal cases are proved. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Real OctahedralTriangles

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}

namespace Development

/-- The selected development separates both opposite pairs, with no remaining angle-case assumption. -/
theorem selected_opposite_petals (net : graph.Development small_faces source slit)
    (source_order : graph.curvature (opposite source) ≤ graph.curvature source)
    (maximal : ∀ i, graph.curvature (fanNeighbor source i) ≤ graph.curvature (fanNeighbor source slit)) :
    net.OppositePetals := by
  have safe (i : Fin 2) : net.Separated (true, i.castSucc.castSucc) (true, i.succ.succ) := by
    by_cases narrow : net.widenedLeft i + net.widenedRight i < π
    · exact net.opposite_petals_caseA_of_paired_poles i source_order narrow
    by_cases fan_wide : π ≤ net.leftFanCorner i + net.rightFanCorner i
    · exact (net.opposite_petals_caseB i (le_of_not_gt narrow) fan_wide).mono interior_subset interior_subset
    have small := lt_of_not_ge fan_wide
    fin_cases i
    · exact net.first_opposite_petals_of_small_fan source_order maximal small
    · exact net.last_opposite_petals_of_small_fan source_order maximal small
  exact ⟨safe 0, safe 1⟩

end Development

/-- Choose the sharper endpoint of one opposite pair and a maximum-curvature slit, then unfold. -/
theorem hasEdgeUnfolding_of_octahedron (graph : P.SixVertexGraph)
    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4)
    (octahedral : graph.kind = .octahedron) : P.HasEdgeUnfolding := by
  obtain ⟨source, _, source_order⟩ := graph.exists_sharper_pole 0
  obtain ⟨slit, maximal, _, _⟩ := graph.exists_curvature_slit small_faces source
  obtain ⟨net⟩ := graph.exists_development small_faces source slit
  exact net.hasEdgeUnfolding_of_two_comparisons octahedral source_order maximal
    (net.selected_opposite_petals source_order maximal)

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
