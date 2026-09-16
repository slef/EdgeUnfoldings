import SixVertexUnfolding.Geometry.OctahedralPatchDirections
import SixVertexUnfolding.OctahedralJunctionIncidence

/-! The first and last slit copies and their copied cut-edge directions in the actual development. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open Real EuclideanGeometry OctahedralTriangles

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

/-- Both copies of the slit edge have this original radial length. -/
noncomputable def slitRadius (_net : graph.Development small_faces source slit) : ℝ :=
  dist (graph.vertex (opposite source) : Space) (graph.vertex (fanNeighbor source slit))

theorem slitRadius_pos : 0 < net.slitRadius := by
  apply dist_pos.mpr
  intro same
  exact ((by decide : ∀ s i, fanNeighbor s i ≠ opposite s) source slit)
    (graph.vertex.injective (Subtype.ext same)).symm

theorem first_slit_position : (net.patch 0).left = net.slitRadius • direction 0 := by
  have paired : fanNeighbor (opposite source) slit = fanNeighbor source slit :=
    (by decide : ∀ s i, fanNeighbor (opposite s) i = fanNeighbor s i) source slit
  rw [net.patch_left]
  simp [openingPoint, openingVertex, openingAngle, slitRadius, paired]

theorem last_slit_position : (net.patch 3).right = net.slitRadius • direction (-graph.curvature (opposite source)) := by
  have paired : fanNeighbor (opposite source) slit = fanNeighbor source slit :=
    (by decide : ∀ s i, fanNeighbor (opposite s) i = fanNeighbor s i) source slit
  have total : graph.totalAngleAt (opposite source) = 2 * π - graph.curvature (opposite source) := by
    unfold curvature
    ring
  rw [net.patch_right]
  change graph.openingPoint (opposite source) slit 4 = _
  rw [openingPoint, graph.openingAngle_last, total, direction_two_pi_sub]
  simp [openingVertex, slitRadius, paired]

/-- The two separated copies of the physical slit vertex retain exactly its full original angle sum. -/
theorem slit_corner_sum : (net.patch 0).leftCorner + (net.patch 3).rightCorner =
    graph.totalAngleAt (fanNeighbor source slit) := by
  unfold DevelopedPatch.leftCorner DevelopedPatch.rightCorner
  rw [(net.patch 0).fan_angle_at_left, (net.patch 0).petal_angle_at_left,
    angle_comm (net.patch 3).pole (net.patch 3).right (net.patch 3).left,
    (net.patch 3).fan_angle_at_right,
    angle_comm (net.patch 3).left (net.patch 3).right (net.patch 3).apex,
    (net.patch 3).petal_angle_at_right]
  have incidence := junction_angle_incidence
    (fun a b c => angle (graph.vertex a : Space) (graph.vertex b : Space) (graph.vertex c : Space))
    (fun a b c => angle_comm _ _ _) source (slit + 3)
  have first : (slit + 3) + 1 = slit := by fin_cases slit <;> decide
  have second : (slit + 3) + 2 = slit + 1 := by fin_cases slit <;> decide
  rw [first, second, ← graph.totalAngleAt_eq_fan_angles] at incidence
  simp only [add_zero, first]
  linarith

theorem last_corner_of_first_reflex (ρ : ℝ) (reflex : (net.patch 0).leftCorner = π + ρ) :
    (net.patch 3).rightCorner = π - graph.curvature (fanNeighbor source slit) - ρ := by
  have sum := net.slit_corner_sum
  rw [reflex] at sum
  unfold curvature
  linarith

theorem first_reflex_bound (ρ : ℝ) (reflex : (net.patch 0).leftCorner = π + ρ) :
    ρ < π - graph.curvature (fanNeighbor source slit) := by
  have positive := (net.patch 3).rightCorner_pos
  rw [net.last_corner_of_first_reflex ρ reflex] at positive
  linarith

theorem first_apex_direction_of_reflex (ρ : ℝ) (reflex : (net.patch 0).leftCorner = π + ρ) :
    (net.patch 0).apex - (net.patch 0).left =
      dist (net.patch 0).apex (net.patch 0).left • direction (-ρ) := by
  rw [net.patch_apex_direction_left, reflex]
  change _ • direction (0 + π - (π + ρ)) = _
  congr 2
  ring

theorem last_apex_direction_of_first_reflex (ρ : ℝ) (reflex : (net.patch 0).leftCorner = π + ρ) :
    (net.patch 3).apex - (net.patch 3).right = dist (net.patch 3).apex (net.patch 3).right •
      direction (-ρ - graph.curvature (fanNeighbor source slit) - graph.curvature (opposite source)) := by
  rw [net.patch_apex_direction_right, net.last_corner_of_first_reflex ρ reflex]
  change _ • direction (graph.openingAngle (opposite source) slit 4 - π +
    (π - graph.curvature (fanNeighbor source slit) - ρ)) = _
  rw [graph.openingAngle_last]
  have expression : graph.totalAngleAt (opposite source) - π +
      (π - graph.curvature (fanNeighbor source slit) - ρ) =
        (-ρ - graph.curvature (fanNeighbor source slit) - graph.curvature (opposite source)) + 2 * π := by
    unfold curvature
    ring
  rw [expression, direction_add_two_pi]

theorem last_base_direction_at_slit : (net.patch 3).left - (net.patch 3).right =
    dist (net.patch 3).left (net.patch 3).right •
      direction (-π - graph.curvature (opposite source) + angle 0 (net.patch 3).right (net.patch 3).left) := by
  rw [net.patch_base_direction_right]
  change _ • direction (graph.openingAngle (opposite source) slit 4 - π + _) = _
  rw [graph.openingAngle_last]
  have expression : graph.totalAngleAt (opposite source) - π + angle 0 (net.patch 3).right (net.patch 3).left =
      (-π - graph.curvature (opposite source) + angle 0 (net.patch 3).right (net.patch 3).left) + 2 * π := by
    unfold curvature
    ring
  rw [expression, direction_add_two_pi]

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
