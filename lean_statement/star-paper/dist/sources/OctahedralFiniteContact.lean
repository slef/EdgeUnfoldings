import SixVertexUnfolding.Geometry.OctahedralSecondContactBudget
import SixVertexUnfolding.Geometry.OctahedralContactParameters
import SixVertexUnfolding.Geometry.OctahedralSelectedLocal

/-! Both closed remote finite-cut exclusions follow from the selected curvature conditions. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open Real EuclideanGeometry OctahedralTriangles

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

theorem first_remote_cut_clear_of_curvature_gate
    (alternative : π ≤ graph.curvature source ∨ graph.curvature (opposite source) ≤ π)
    (threshold : π ≤ 2 * graph.curvature (fanNeighbor source slit) + graph.curvature (opposite source))
    (gate : π ≤ graph.curvature source ∨
      π ≤ graph.curvature (fanNeighbor source (slit + 1)) + graph.curvature (fanNeighbor source slit) +
        graph.curvature (opposite source)) :
    Disjoint (net.placedTriangle (true, 1)) (segment ℝ 0 (net.patch 3).right) := by
  apply Set.disjoint_left.mpr
  intro x petal contact
  obtain ⟨t, positive, upper, on_cut⟩ := net.first_remote_contact_parameter alternative x petal contact
  have E1 := net.source_curvature_lt_pi_of_first_cut_edge_contact alternative threshold t positive upper on_cut
  have E2 := net.first_cut_contact_curvature_budget alternative threshold t positive upper on_cut
  exact Curvature.finite_contact_impossible gate (graph.curvature_pos small_faces (opposite source))
    (angle_pos_of_not_collinear (net.patch 0).petal_noncollinear) E1 E2

theorem second_remote_cut_clear_of_curvature_gate
    (alternative : π ≤ graph.curvature source ∨ graph.curvature (opposite source) ≤ π)
    (threshold : π ≤ 2 * graph.curvature (fanNeighbor source slit) + graph.curvature (opposite source))
    (gate : π ≤ graph.curvature source ∨
      π ≤ graph.curvature (fanNeighbor source (slit + 3)) + graph.curvature (fanNeighbor source slit) +
        graph.curvature (opposite source)) :
    Disjoint (net.placedTriangle (true, 2)) (segment ℝ 0 (net.patch 0).left) := by
  apply Set.disjoint_left.mpr
  intro x petal contact
  have reflex := net.second_remote_contact_forces_reflex alternative x petal contact
  obtain ⟨t, positive, upper, on_cut⟩ := net.second_remote_contact_parameter alternative x petal contact
  have E1 := net.source_curvature_lt_pi_of_second_cut_contact alternative threshold reflex t positive upper on_cut
  have E2 := net.second_cut_contact_curvature_budget alternative threshold t positive upper on_cut
  have noncollinear : ¬ Collinear ℝ ({(net.patch 3).right, (net.patch 3).left, (net.patch 3).apex} : Set Plane) := by
    rw [Set.insert_comm]
    exact (net.patch 3).petal_noncollinear
  exact Curvature.finite_contact_impossible gate (graph.curvature_pos small_faces (opposite source))
    (angle_pos_of_not_collinear noncollinear) E1 E2

include small_faces in
/-- Every maximum-curvature equator choice supplies both remote contact gates, including ties. -/
theorem selected_remote_contact_gates
    (maximal : ∀ i, graph.curvature (fanNeighbor source i) ≤ graph.curvature (fanNeighbor source slit)) :
    (π ≤ graph.curvature source ∨
      π ≤ graph.curvature (fanNeighbor source (slit + 1)) + graph.curvature (fanNeighbor source slit) + graph.curvature (opposite source)) ∧
    (π ≤ graph.curvature source ∨
      π ≤ graph.curvature (fanNeighbor source (slit + 3)) + graph.curvature (fanNeighbor source slit) + graph.curvature (opposite source)) := by
  by_cases source_high : π ≤ graph.curvature source
  · exact ⟨Or.inl source_high, Or.inl source_high⟩
  have fan_pos := graph.curvature_pos small_faces (opposite source)
  have first_pos := graph.curvature_pos small_faces (fanNeighbor source (slit + 1))
  have third_pos := graph.curvature_pos small_faces (fanNeighbor source (slit + 3))
  refine ⟨Or.inr ?_, Or.inr ?_⟩ <;>
    have total := graph.curvature_poles_equator source
  all_goals
    have rotated : (∑ j : Fin 4, graph.curvature (fanNeighbor source (slit + j))) =
        ∑ j : Fin 4, graph.curvature (fanNeighbor source j) := by
      fin_cases slit <;> simp [Fin.sum_univ_four] <;> ring
    rw [← rotated, Fin.sum_univ_four] at total
    simp only [add_zero] at total
    by_cases slit_high : π ≤ graph.curvature (fanNeighbor source slit)
    · linarith
    · linarith [maximal (slit + 1), maximal (slit + 2), maximal (slit + 3)]

/-- No finite-cut nonoverlap premise remains for the selected source and slit. -/
theorem selected_finite_cuts_clear
    (source_order : graph.curvature (opposite source) ≤ graph.curvature source)
    (maximal : ∀ i, graph.curvature (fanNeighbor source i) ≤ graph.curvature (fanNeighbor source slit)) :
    net.FiniteCutsClear := by
  have alternative := Curvature.half_fan_alternative source_order
  have threshold := (selected_slit_threshold (small_faces := small_faces) maximal).le
  have gates := selected_remote_contact_gates (small_faces := small_faces) maximal
  refine ⟨?_, ?_⟩
  · simpa only [net.patch_right] using net.first_remote_cut_clear_of_curvature_gate alternative threshold gates.1
  · simpa only [net.patch_left] using net.second_remote_cut_clear_of_curvature_gate alternative threshold gates.2

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
