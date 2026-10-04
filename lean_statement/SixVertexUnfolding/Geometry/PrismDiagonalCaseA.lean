import SixVertexUnfolding.Geometry.PrismDiagonalCapCornerCones
import SixVertexUnfolding.Geometry.PrismDiagonalCapAngles
import SixVertexUnfolding.Geometry.TwoFanCaseA

/-! The actual fallback's Case A comparison in both cap views. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Prism Prism.FaceLabel Real

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
variable (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4)

/-- The cap's two cut-ray directions, widened by its base curvatures, have this total. -/
noncomputable def prismCapOpening (q : Fin 2) : ℝ :=
  π - graph.prismAngle small_faces (capFace q) (capSource q) +
    (graph.curvature (vertexLabel (capLeftVertex q)) + graph.curvature (vertexLabel (capRightVertex q)))

variable (prism_kind : graph.kind = .prismDiagonal)
include prism_kind

/-- The three angles of the actual cap triangle sum to π. -/
theorem prism_cap_triangle_angles (q : Fin 2) :
    graph.prismAngle small_faces (capFace q) (capLeftVertex q) +
      graph.prismAngle small_faces (capFace q) (capRightVertex q) +
      graph.prismAngle small_faces (capFace q) (capSource q) = π := by
  have total := graph.prismAngle_sum small_faces prism_kind (capFace q)
  fin_cases q <;>
    simp [capFace, capLeftVertex, capRightVertex, capSource, Fin.sum_univ_succ,
      graph.prismAngle_zero small_faces prism_kind, faceVertices] at total ⊢ <;> linarith

/-- At either source, the two whole quadrilateral angles and the cap angle exhaust the surface angle. -/
theorem prism_cap_source_angles (q : Fin 2) :
    graph.prismAngle small_faces (capLeftFace q) (capSource q) +
      graph.prismAngle small_faces (capRightFace q) (capSource q) +
      graph.prismAngle small_faces (capFace q) (capSource q) =
        2 * π - graph.curvature (vertexLabel (capSource q)) := by
  fin_cases q
  · exact graph.prism_lower_source_angles small_faces prism_kind
  · have h := graph.prism_upper_source_angles small_faces prism_kind
    change graph.prismAngle small_faces D 5 + graph.prismAngle small_faces B 5 +
      graph.prismAngle small_faces F 5 = 2 * π - graph.curvature (vertexLabel 5)
    linarith

/-- The opening agrees with the two directions derived from the actual fans. -/
theorem prismCapOpening_eq (q : Fin 2) :
    graph.prismCapOpening small_faces q =
      (graph.prismAngle small_faces (capFace q) (capLeftVertex q) + graph.curvature (vertexLabel (capLeftVertex q))) +
      (graph.prismAngle small_faces (capFace q) (capRightVertex q) + graph.curvature (vertexLabel (capRightVertex q))) := by
  unfold prismCapOpening
  linarith [graph.prism_cap_triangle_angles small_faces prism_kind q]

variable {graph small_faces}

/-- Both explicit wider-angle bounds separate the actual whole quadrilaterals in Case A. -/
theorem PrismFallbackDevelopment.cap_caseA (net : graph.PrismFallbackDevelopment small_faces) (q : Fin 2)
    (narrow : graph.prismCapOpening small_faces q < π)
    (left_bound : graph.prismAngle small_faces (capLeftFace q) (capSource q) ≤
      (π + graph.prismCapOpening small_faces q) / 2)
    (right_bound : graph.prismAngle small_faces (capRightFace q) (capSource q) ≤
      (π + graph.prismCapOpening small_faces q) / 2) :
    Disjoint (interior (net.place (capLeftFace q) '' (graph.prismDiagonalFace small_faces (capLeftFace q)).val))
      (interior (net.place (capRightFace q) '' (graph.prismDiagonalFace small_faces (capRightFace q)).val)) := by
  have shared := net.cap_shared_triangle prism_kind q
  have turns := net.cap_one_turn prism_kind q
  have lengths := net.cap_copied_lengths prism_kind q
  have directions := net.cap_directions prism_kind q
  have witnesses := net.cap_corner_witnesses prism_kind q
  have angles := net.cap_corner_angles prism_kind q
  have left_bounds := graph.prismAngle_bounds small_faces prism_kind (capLeftFace q) (capSource q) (by fin_cases q <;> decide)
  have right_bounds := graph.prismAngle_bounds small_faces prism_kind (capRightFace q) (capSource q) (by fin_cases q <;> decide)
  have source := graph.prism_cap_source_angles small_faces prism_kind q
  have source_pos := graph.curvature_pos small_faces (vertexLabel (capSource q))
  have left_pos := graph.curvature_pos small_faces (vertexLabel (capLeftVertex q))
  have right_pos := graph.curvature_pos small_faces (vertexLabel (capRightVertex q))
  have angle_sum : graph.prismAngle small_faces (capLeftFace q) (capSource q) +
      graph.prismAngle small_faces (capRightFace q) (capSource q) < π + graph.prismCapOpening small_faces q := by
    unfold prismCapOpening
    linarith
  rw [graph.prismCapOpening_eq small_faces prism_kind q] at narrow left_bound right_bound angle_sum
  exact two_fan_caseA (net.capLeftFan prism_kind q) (net.capRightFan prism_kind q)
    shared.1 shared.2.1 shared.2.2 turns.1 turns.2 lengths.1 lengths.2
    _ _ (net.place (capLeftFace q) (graph.prismVertex (capOtherSource q)))
    (net.place (capRightFace q) (graph.prismVertex (capOtherSource q)))
    (net.cap_left_corner_cone prism_kind q) (net.cap_right_corner_cone prism_kind q)
    witnesses.1 witnesses.2 _ _ _ _ directions.1 directions.2 angles.1 angles.2
    left_bounds.1 left_bounds.2 right_bounds.1 right_bounds.2 narrow angle_sum left_bound right_bound

/-- A cap-curvature sum at least π automatically supplies both wider-angle bounds. -/
theorem PrismFallbackDevelopment.cap_caseA_of_high_cap
    (net : graph.PrismFallbackDevelopment small_faces) (q : Fin 2)
    (high : π ≤ graph.curvature (vertexLabel (capLeftVertex q)) +
      graph.curvature (vertexLabel (capRightVertex q)) + graph.curvature (vertexLabel (capSource q)))
    (narrow : graph.prismCapOpening small_faces q < π) :
    Disjoint (interior (net.place (capLeftFace q) '' (graph.prismDiagonalFace small_faces (capLeftFace q)).val))
      (interior (net.place (capRightFace q) '' (graph.prismDiagonalFace small_faces (capRightFace q)).val)) := by
  have source := graph.prism_cap_source_angles small_faces prism_kind q
  have left_bounds := graph.prismAngle_bounds small_faces prism_kind (capLeftFace q) (capSource q) (by fin_cases q <;> decide)
  have right_bounds := graph.prismAngle_bounds small_faces prism_kind (capRightFace q) (capSource q) (by fin_cases q <;> decide)
  apply net.cap_caseA prism_kind q narrow <;> unfold prismCapOpening <;> linarith [left_bounds.1, left_bounds.2, right_bounds.1, right_bounds.2]

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
