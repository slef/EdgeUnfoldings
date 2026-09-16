import SixVertexUnfolding.Geometry.OctahedralFiniteContact
import SixVertexUnfolding.Geometry.OctahedralOppositeAngles

/-! The actual slit-adjacent apex angles are too small for the proposed pocket obstruction. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open Real EuclideanGeometry OctahedralTriangles

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

/-- Every developed apex angle satisfies the strict spatial link bound at the source. -/
theorem petal_apex_link (i : Fin 4) :
    2 * net.petalApexAngle i < 2 * π - graph.curvature source := by
  rw [net.petalApexAngle_eq]
  apply graph.vertex_angle_lt_half_deficit small_faces
  · exact fanNeighbor_ne_source source (slit + i)
  · exact fanNeighbor_ne_source source ((slit + i) + 1)
  · exact (by decide : ∀ s j, fanNeighbor s j ≠ opposite s) source (slit + i)

/-- The curvature gate and strict link bound put any apex below its pocket budget. -/
theorem apex_lt_pocket_budget (i : Fin 4) (a : Fin 6)
    (threshold : π ≤ 2 * graph.curvature (fanNeighbor source slit) + graph.curvature (opposite source))
    (gate : π ≤ graph.curvature source ∨
      π ≤ graph.curvature a + graph.curvature (fanNeighbor source slit) + graph.curvature (opposite source)) :
    net.petalApexAngle i <
      graph.curvature a + graph.curvature (fanNeighbor source slit) + graph.curvature (opposite source) := by
  rcases gate with source_high | budget_high
  · have link := net.petal_apex_link i
    have a_pos := graph.curvature_pos small_faces a
    have fan_pos := graph.curvature_pos small_faces (opposite source)
    linarith
  · exact (net.petalApexAngle_lt_pi i).trans_le budget_high

/-- Both orientations of a small-fan pocket would contradict these proved strict bounds. -/
theorem selected_pocket_angle_bounds
    (maximal : ∀ i, graph.curvature (fanNeighbor source i) ≤ graph.curvature (fanNeighbor source slit)) :
    net.petalApexAngle 0 < graph.curvature (fanNeighbor source (slit + 1)) +
        graph.curvature (fanNeighbor source slit) + graph.curvature (opposite source) ∧
      net.petalApexAngle 3 < graph.curvature (fanNeighbor source (slit + 3)) +
        graph.curvature (fanNeighbor source slit) + graph.curvature (opposite source) := by
  have threshold := (selected_slit_threshold (small_faces := small_faces) maximal).le
  have gates := selected_remote_contact_gates (small_faces := small_faces) maximal
  exact ⟨net.apex_lt_pocket_budget 0 _ threshold gates.1, net.apex_lt_pocket_budget 3 _ threshold gates.2⟩

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
