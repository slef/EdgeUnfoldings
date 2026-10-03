import SixVertexUnfolding.Geometry.PrismDiagonalAngleSums
import SixVertexUnfolding.Curvature.Prism

/-! The sharp-end switch's angle identities for actual convex prism-with-diagonal
solids. These certify the angle alternatives, not yet the candidate nets. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Prism Prism.FaceLabel Real

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
variable (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4)

/-- The sum of curvatures at the common base of the two compared views. -/
noncomputable def prismSwitchBaseCurvature : ℝ :=
  graph.curvature (vertexLabel 3) + graph.curvature (vertexLabel 4)

/-- The near-star's wider-angle deficit at its source, manuscript vertex 1. -/
noncomputable def prismNearDeficit (f : FaceLabel) : ℝ :=
  2 * graph.prismAngle small_faces f 1 + graph.prismAngle small_faces E 1 -
    2 * π - graph.prismSwitchBaseCurvature

/-- The fallback's upper-view deficit at manuscript vertex 5. -/
noncomputable def prismFallbackDeficit (f : FaceLabel) : ℝ :=
  2 * graph.prismAngle small_faces f 5 + graph.prismAngle small_faces F 5 -
    2 * π - graph.prismSwitchBaseCurvature

/-- Strict slack between twice a full face angle and its vertex's surface angle. -/
noncomputable def prismLinkSlack (f : FaceLabel) (i : Fin 6) : ℝ :=
  (2 * π - graph.curvature (vertexLabel i)) - 2 * graph.prismAngle small_faces f i

variable (prism_kind : graph.kind = .prismDiagonal)
include prism_kind

theorem prismLinkSlack_pos (f : FaceLabel) (i : Fin 6) (member : i ∈ faceVertices f) :
    0 < graph.prismLinkSlack small_faces f i :=
  sub_pos.mpr (graph.prismAngle_link_bound small_faces prism_kind f i member)

/-- The three positive-remainder identities of Switch 1, now for geometric face angles. -/
theorem prism_switch_one_identities :
    -graph.prismNearDeficit small_faces C =
      graph.prismAngle small_faces C 0 + graph.prismAngle small_faces F 5 +
      (π - graph.prismAngle small_faces B 3) + (π - graph.prismAngle small_faces C 1) +
      (π - graph.prismAngle small_faces D 4) ∧
    -graph.prismNearDeficit small_faces D - graph.prismFallbackDeficit small_faces D =
      2 * graph.prismAngle small_faces D 2 + graph.prismAngle small_faces E 1 +
      graph.prismAngle small_faces F 5 + 2 * (π - graph.prismAngle small_faces B 3) +
      2 * (π - graph.prismAngle small_faces C 3) ∧
    -graph.prismNearDeficit small_faces D - graph.prismFallbackDeficit small_faces B =
      graph.prismLinkSlack small_faces A 0 + graph.prismLinkSlack small_faces A 2 +
      graph.prismLinkSlack small_faces B 5 + graph.curvature (vertexLabel 1) +
      2 * graph.prismAngle small_faces C 1 + (π - graph.prismAngle small_faces B 3) +
      (π - graph.prismAngle small_faces C 3) + (π - graph.prismAngle small_faces D 4) +
      2 * (graph.prismAngle small_faces E 1 - π / 2) := by
  have A_sum := graph.prismAngle_sum small_faces prism_kind A
  have B_sum := graph.prismAngle_sum small_faces prism_kind B
  have C_sum := graph.prismAngle_sum small_faces prism_kind C
  have D_sum := graph.prismAngle_sum small_faces prism_kind D
  have E_sum := graph.prismAngle_sum small_faces prism_kind E
  have F_sum := graph.prismAngle_sum small_faces prism_kind F
  simp [Fin.sum_univ_succ, faceVertices, graph.prismAngle_zero small_faces prism_kind] at A_sum B_sum C_sum D_sum E_sum F_sum
  unfold prismNearDeficit prismFallbackDeficit prismLinkSlack prismSwitchBaseCurvature
  simp only [graph.prism_curvature_eq small_faces prism_kind, sum_faces]
  simp [graph.prismAngle_zero small_faces prism_kind, faceVertices]
  exact ⟨by linarith, by linarith, by linarith⟩

/-- One of the near-star's two wider-angle tests always holds strictly. -/
theorem prism_near_C_deficit_neg : graph.prismNearDeficit small_faces C < 0 := by
  have identities := graph.prism_switch_one_identities small_faces prism_kind
  have C0 := graph.prismAngle_bounds small_faces prism_kind C 0 (by decide)
  have F5 := graph.prismAngle_bounds small_faces prism_kind F 5 (by decide)
  have B3 := graph.prismAngle_bounds small_faces prism_kind B 3 (by decide)
  have C1 := graph.prismAngle_bounds small_faces prism_kind C 1 (by decide)
  have D4 := graph.prismAngle_bounds small_faces prism_kind D 4 (by decide)
  linarith [identities.1]

/-- When the near-star fails its other two tests, both fallback deficits are negative. -/
theorem prism_failed_near_forces_fallback_bounds
    (middle_obtuse : π / 2 < graph.prismAngle small_faces E 1)
    (near_fails : 0 < graph.prismNearDeficit small_faces D) :
    graph.prismFallbackDeficit small_faces B < 0 ∧
      graph.prismFallbackDeficit small_faces D < 0 := by
  have identities := graph.prism_switch_one_identities small_faces prism_kind
  have D2 := graph.prismAngle_bounds small_faces prism_kind D 2 (by decide)
  have E1 := graph.prismAngle_bounds small_faces prism_kind E 1 (by decide)
  have F5 := graph.prismAngle_bounds small_faces prism_kind F 5 (by decide)
  have B3 := graph.prismAngle_bounds small_faces prism_kind B 3 (by decide)
  have C3 := graph.prismAngle_bounds small_faces prism_kind C 3 (by decide)
  have C1 := graph.prismAngle_bounds small_faces prism_kind C 1 (by decide)
  have D4 := graph.prismAngle_bounds small_faces prism_kind D 4 (by decide)
  have A0_link := graph.prismLinkSlack_pos small_faces prism_kind A 0 (by decide)
  have A2_link := graph.prismLinkSlack_pos small_faces prism_kind A 2 (by decide)
  have B5_link := graph.prismLinkSlack_pos small_faces prism_kind B 5 (by decide)
  have curvature_pos := graph.curvature_pos small_faces (vertexLabel 1)
  constructor
  · linarith [identities.2.2]
  · linarith [identities.2.1]

/-- The actual solid supplies a nonobtuse middle, two near-star bounds, or two fallback bounds.
Nonoverlap of the corresponding original-face developments remains a separate step. -/
theorem prism_switch_one_angle_alternative :
    graph.prismAngle small_faces E 1 ≤ π / 2 ∨
    (graph.prismNearDeficit small_faces C ≤ 0 ∧ graph.prismNearDeficit small_faces D ≤ 0) ∨
    (graph.prismFallbackDeficit small_faces B < 0 ∧ graph.prismFallbackDeficit small_faces D < 0) := by
  by_cases middle : graph.prismAngle small_faces E 1 ≤ π / 2
  · exact Or.inl middle
  · by_cases near : graph.prismNearDeficit small_faces D ≤ 0
    · exact Or.inr (Or.inl ⟨(graph.prism_near_C_deficit_neg small_faces prism_kind).le, near⟩)
    · exact Or.inr (Or.inr (graph.prism_failed_near_forces_fallback_bounds small_faces prism_kind
        (lt_of_not_ge middle) (lt_of_not_ge near)))

/-- The two middle angles in Switch 2 are angles of the same actual triangular cap. -/
theorem prism_switch_two_angle_alternative :
    graph.prismAngle small_faces F 3 ≤ π / 2 ∨ graph.prismAngle small_faces F 5 ≤ π / 2 := by
  have total := graph.prismAngle_sum small_faces prism_kind F
  simp [Fin.sum_univ_succ, faceVertices, graph.prismAngle_zero small_faces prism_kind] at total
  have positive := (graph.prismAngle_bounds small_faces prism_kind F 4 (by decide)).1
  apply Prism.one_middle_angle_nonobtuse (c := graph.prismAngle small_faces F 4)
  · linarith
  · exact positive

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
