import SixVertexUnfolding.Geometry.OctahedralHighFan
import SixVertexUnfolding.Geometry.OctahedralCaseA
import SixVertexUnfolding.Geometry.OctahedralCaseB
import SixVertexUnfolding.Geometry.OctahedralPairedCaseA

/-! A completed original-edge unfolding theorem for the high-fan branch outside the small-fan pocket cases. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open Real OctahedralTriangles

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

/-- Under the usual source rule, only a small-fan pocket can remain in either opposite-petal comparison. -/
theorem opposite_petals_of_caseAB (source_rule : π ≤ graph.curvature source ∨ ∀ v, graph.curvature v ≤ π)
    (cases : ∀ i : Fin 2, net.widenedLeft i + net.widenedRight i < π ∨
      π ≤ net.leftFanCorner i + net.rightFanCorner i) : net.OppositePetals := by
  have safe (i : Fin 2) :
      Disjoint (net.placedTriangle (true, i.castSucc.castSucc)) (net.placedTriangle (true, i.succ.succ)) := by
    by_cases narrow : net.widenedLeft i + net.widenedRight i < π
    · exact net.opposite_petals_caseA_of_source_rule i source_rule narrow
    · exact net.opposite_petals_caseB i (le_of_not_gt narrow) ((cases i).resolve_left narrow)
  exact ⟨(safe 0).mono interior_subset interior_subset, (safe 1).mono interior_subset interior_subset⟩

/-- Every comparison and every original-edge certificate obligation is discharged in this stated angle region. -/
theorem hasEdgeUnfolding_of_high_fan_and_caseAB (octahedral : graph.kind = .octahedron)
    (source_order : graph.curvature (opposite source) ≤ graph.curvature source)
    (fan_high : π ≤ graph.curvature (opposite source))
    (cases : ∀ i : Fin 2, net.widenedLeft i + net.widenedRight i < π ∨
      π ≤ net.leftFanCorner i + net.rightFanCorner i) : P.HasEdgeUnfolding := by
  have source_high : π ≤ graph.curvature source := fan_high.trans source_order
  exact net.hasEdgeUnfolding_of_high_fan (Or.inl source_high) fan_high octahedral
    (net.opposite_petals_of_caseAB (Or.inl source_high) cases)

/-- The stronger paired-pole rule removes the global source-curvature alternative from Case A. -/
theorem opposite_petals_of_paired_caseAB
    (source_order : graph.curvature (opposite source) ≤ graph.curvature source)
    (cases : ∀ i : Fin 2, net.widenedLeft i + net.widenedRight i < π ∨
      π ≤ net.leftFanCorner i + net.rightFanCorner i) : net.OppositePetals := by
  have safe (i : Fin 2) : net.Separated (true, i.castSucc.castSucc) (true, i.succ.succ) := by
    by_cases narrow : net.widenedLeft i + net.widenedRight i < π
    · exact net.opposite_petals_caseA_of_paired_poles i source_order narrow
    · exact (net.opposite_petals_caseB i (le_of_not_gt narrow) ((cases i).resolve_left narrow)).mono
        interior_subset interior_subset
  exact ⟨safe 0, safe 1⟩

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
