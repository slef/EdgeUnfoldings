import SixVertexUnfolding.Geometry.SmallPolyhedronCutTreeCurvature
import SixVertexUnfolding.Geometry.VertexFanCutTreeConeCoverage
import SixVertexUnfolding.Geometry.SmallPolyhedronJunctionAngleSum

/-! The source-angle budget for the six-vertex universal-source case.
Local cone coverage, flat junction sums, and the global curvature bound
all come from the actual polyhedron, with no canonical graph assumption. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set Real

variable {P : ConvexPolyhedron} [Fintype P.Face]
  (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)
  {a : frontier P.body} (T : P.CutLocusTree a)
  [Fintype T.vertices] [DecidableRel T.graph.Adj]
  (models : (d : T.graph.Dart) → CutEdgeMetricModel T d.adj)

include size small_faces in
/-- The original face-angle sum is bounded by all actual incident tree triangles. -/
theorem small_incident_angles_cover_surfaceAngle (u : T.vertices) (v : P.Vertex)
    (at_vertex : (u : Space) = (v : Space)) :
    P.surfaceAngle v ≤ T.incidentAngleSum models u := by
  have degree := P.edgeGraph_min_degree v
  letI : NeZero (P.edgeGraph.degree v) := ⟨by omega⟩
  obtain ⟨fan⟩ := P.exists_vertex_face_fan size small_faces v rfl
  rw [← fan.totalAngle_eq_surfaceAngle size small_faces]
  exact fan.incident_model_angles_cover_cone size small_faces a T models u at_vertex

include size small_faces in
/-- Tree angle accounting needs only a total-curvature upper bound. -/
theorem small_source_angle_sum_le_of_curvature_bound
    (curvature_bound : (∑ v : P.Vertex, P.vertexCurvature v) ≤ 4 * π)
    (source : P.Vertex) (at_source : (a : Space) = (source : Space)) :
    (∑ d, (models d).sourceAngle) ≤ P.surfaceAngle source := by
  classical
  have at_vertex (u : T.vertices) :
      2 * π - T.originalCurvature u ≤ T.incidentAngleSum models u := by
    by_cases original : (u : Space) ∈ P.vertices
    · let v : P.Vertex := ⟨u, original⟩
      rw [T.originalCurvature_at_vertex u v rfl, vertexCurvature, sub_sub_cancel]
      exact small_incident_angles_cover_surfaceAngle size small_faces T models u v rfl
    · rw [T.originalCurvature_at_nonvertex u original, sub_zero]
      exact (small_sum_nonvertex_junction_angles size small_faces a T u original
        (fun v => models (T.graph.dartOfNeighborSet u v))).ge
  have total := Finset.sum_le_sum (fun u (_ : u ∈ Finset.univ) => at_vertex u)
  rw [Finset.sum_sub_distrib, T.sum_originalCurvature source at_source] at total
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at total
  rw [show P.vertexCurvature source = 2 * π - P.surfaceAngle source from rfl] at total
  have accounting := T.sum_source_and_vertex_angles models
  linarith

include small_faces in
/-- The complete source-angle budget for six vertices and a universal source. -/
theorem universal_source_angle_sum_le (six : P.vertices.card = 6)
    (source : P.Vertex) (universal : ∀ v : P.Vertex, v ≠ source → P.edgeGraph.Adj source v)
    (at_source : (a : Space) = (source : Space)) :
    (∑ d, (models d).sourceAngle) ≤ P.surfaceAngle source :=
  small_source_angle_sum_le_of_curvature_bound (by omega) small_faces T models
    (universal_sum_vertexCurvature_le six small_faces source universal) source at_source

include small_faces in
/-- Each kite is counted twice by the directed sum; the half-sum is strictly below π. -/
theorem universal_half_source_angle_sum_lt_pi (six : P.vertices.card = 6)
    (source : P.Vertex) (universal : ∀ v : P.Vertex, v ≠ source → P.edgeGraph.Adj source v)
    (at_source : (a : Space) = (source : Space)) :
    (∑ d, (models d).sourceAngle) / 2 < π := by
  have bound := universal_source_angle_sum_le small_faces T models six source universal at_source
  have strict := surfaceAngle_lt_two_pi (show P.vertices.card ≤ 6 by omega) small_faces source
  linarith

end SixVertexUnfolding.ConvexPolyhedron
