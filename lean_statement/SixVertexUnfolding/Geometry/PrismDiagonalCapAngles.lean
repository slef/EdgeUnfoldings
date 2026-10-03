import SixVertexUnfolding.Geometry.PrismDiagonalSwitchAngles

/-! The cap rule for actual original-face angles. These bounds will supply the
fallback's two Case A views once its geometric comparison is constructed. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Prism Prism.FaceLabel Real

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)

noncomputable def prismLowerCapCurvature : ℝ :=
  graph.curvature (vertexLabel 0) + graph.curvature (vertexLabel 1) + graph.curvature (vertexLabel 2)

noncomputable def prismUpperCapCurvature : ℝ :=
  graph.curvature (vertexLabel 3) + graph.curvature (vertexLabel 4) + graph.curvature (vertexLabel 5)

/-- The two actual cap-curvature sums partition the total curvature of the solid. -/
theorem prism_cap_curvature_sum :
    graph.prismLowerCapCurvature + graph.prismUpperCapCurvature = 4 * π := by
  have total : (∑ i : Fin 6, graph.curvature (vertexLabel i)) = 4 * π := by
    rw [vertexLabel.sum_comp, graph.sum_curvature]
  simp [Fin.sum_univ_succ] at total
  unfold prismLowerCapCurvature prismUpperCapCurvature
  linarith

/-- The cap split covers every actual shape, with equality assigned to the first branch. -/
theorem prism_cap_cases :
    (π ≤ graph.prismLowerCapCurvature ∧ π ≤ graph.prismUpperCapCurvature) ∨
    (3 * π < graph.prismLowerCapCurvature ∧ graph.prismUpperCapCurvature < π) ∨
    (3 * π < graph.prismUpperCapCurvature ∧ graph.prismLowerCapCurvature < π) :=
  Prism.cap_cases graph.prism_cap_curvature_sum

variable (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4)
variable (prism_kind : graph.kind = .prismDiagonal)
include prism_kind

/-- At the lower degree-three source, the three full angles exhaust its surface angle. -/
theorem prism_lower_source_angles :
    graph.prismAngle small_faces B 2 + graph.prismAngle small_faces D 2 +
      graph.prismAngle small_faces A 2 = 2 * π - graph.curvature (vertexLabel 2) := by
  rw [graph.prism_curvature_eq small_faces prism_kind, sum_faces]
  simp [graph.prismAngle_zero small_faces prism_kind, faceVertices]
  ring

/-- The corresponding identity at the upper degree-three source. -/
theorem prism_upper_source_angles :
    graph.prismAngle small_faces B 5 + graph.prismAngle small_faces D 5 +
      graph.prismAngle small_faces F 5 = 2 * π - graph.curvature (vertexLabel 5) := by
  rw [graph.prism_curvature_eq small_faces prism_kind, sum_faces]
  simp [graph.prismAngle_zero small_faces prism_kind, faceVertices]

/-- A lower cap sum at least π supplies both full outer-face angle bounds. -/
theorem prism_lower_cap_wider_bounds (high : π ≤ graph.prismLowerCapCurvature) :
    2 * graph.prismAngle small_faces B 2 + graph.prismAngle small_faces A 2 <
      2 * π + graph.curvature (vertexLabel 0) + graph.curvature (vertexLabel 1) ∧
    2 * graph.prismAngle small_faces D 2 + graph.prismAngle small_faces A 2 <
      2 * π + graph.curvature (vertexLabel 0) + graph.curvature (vertexLabel 1) := by
  have B2 := graph.prismAngle_bounds small_faces prism_kind B 2 (by decide)
  have D2 := graph.prismAngle_bounds small_faces prism_kind D 2 (by decide)
  have bounds := Prism.cap_wider_bounds (graph.prism_lower_source_angles small_faces prism_kind)
    B2.1 B2.2 D2.1 D2.2
    (K := graph.curvature (vertexLabel 0) + graph.curvature (vertexLabel 1))
    (by unfold prismLowerCapCurvature at high; linarith)
  exact ⟨by linarith [bounds.1], by linarith [bounds.2]⟩

/-- An upper cap sum at least π supplies the fallback's two upper-view bounds. -/
theorem prism_upper_cap_wider_bounds (high : π ≤ graph.prismUpperCapCurvature) :
    graph.prismFallbackDeficit small_faces B < 0 ∧ graph.prismFallbackDeficit small_faces D < 0 := by
  have B5 := graph.prismAngle_bounds small_faces prism_kind B 5 (by decide)
  have D5 := graph.prismAngle_bounds small_faces prism_kind D 5 (by decide)
  have bounds := Prism.cap_wider_bounds (graph.prism_upper_source_angles small_faces prism_kind)
    B5.1 B5.2 D5.1 D5.2 (K := graph.prismSwitchBaseCurvature)
    (by unfold prismUpperCapCurvature prismSwitchBaseCurvature at *; linarith)
  unfold prismFallbackDeficit
  exact ⟨by linarith [bounds.1], by linarith [bounds.2]⟩

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
