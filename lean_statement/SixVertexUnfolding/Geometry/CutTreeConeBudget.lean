import SixVertexUnfolding.Geometry.CutTreeCurvature
import SixVertexUnfolding.Geometry.OctahedralCurvature

/-! Reduce the total source-angle bound to local coverage inequalities
at the five original nonsource vertices. The flat junction sums, edge
reversal, tree count, and curvature sum are all proved, not hypotheses.
The cone inequalities are discharged in `CutTreeConeCoverage`; the
result without that premise is `CutTreeSourceBudget`. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Real Set
open scoped BigOperators

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)
  {a : frontier P.body} (T : P.CutLocusTree a)
  [Fintype T.vertices] [DecidableRel T.graph.Adj]
  (models : (d : T.graph.Dart) → CutEdgeMetricModel T d.adj)

include small_faces in
/-- Local cone coverage is sufficient for the full directed source-angle bound. -/
theorem source_angle_sum_le_of_cone_coverage (source : Fin 6)
    (at_source : (a : Space) = (graph.vertex source : Space))
    (cones : ∀ (u : T.vertices) (i : Fin 6), (u : Space) = (graph.vertex i : Space) →
      graph.totalAngleAt i ≤ T.incidentAngleSum models u) :
    ∑ d, (models d).sourceAngle ≤ graph.totalAngleAt source := by
  classical
  have at_vertex (u : T.vertices) :
      2 * π - graph.cutTreeCurvature T u ≤ T.incidentAngleSum models u := by
    by_cases original : (u : Space) ∈ P.vertices
    · obtain ⟨i, equal⟩ := graph.vertex.surjective ⟨u, original⟩
      have at_i : (u : Space) = (graph.vertex i : Space) := (congrArg Subtype.val equal).symm
      rw [graph.cutTreeCurvature_at_original T u i at_i, curvature]
      simpa only [sub_sub_cancel] using cones u i at_i
    · rw [graph.cutTreeCurvature_at_nonvertex T u original, sub_zero]
      exact (graph.sum_nonvertex_junction_angles small_faces a T u original
        (fun v => models (T.graph.dartOfNeighborSet u v))).ge
  have total := Finset.sum_le_sum (fun u (_ : u ∈ Finset.univ) => at_vertex u)
  rw [Finset.sum_sub_distrib, graph.sum_cutTreeCurvature T source at_source] at total
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at total
  have accounting := T.sum_source_and_vertex_angles models
  rw [curvature] at total
  linarith

include small_faces in
/-- Half the directed sum counts each kite once. Cone coverage makes
that total strictly smaller than π at an original convex source. -/
theorem half_source_angle_sum_lt_pi_of_cone_coverage (source : Fin 6)
    (at_source : (a : Space) = (graph.vertex source : Space))
    (cones : ∀ (u : T.vertices) (i : Fin 6), (u : Space) = (graph.vertex i : Space) →
      graph.totalAngleAt i ≤ T.incidentAngleSum models u) :
    (∑ d, (models d).sourceAngle) / 2 < π := by
  have bound := graph.source_angle_sum_le_of_cone_coverage small_faces T models source at_source cones
  have positive := graph.curvature_pos small_faces source
  rw [curvature] at positive
  linarith

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
