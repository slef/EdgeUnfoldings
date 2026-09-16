import SixVertexUnfolding.Geometry.OctahedralConvexSlit
import SixVertexUnfolding.Geometry.RadialPatchHeight

/-! A reflex patch stays strictly inside the ray through its copied cut edge, viewed from the fan pole. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open Real EuclideanGeometry OctahedralTriangles

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

theorem first_reflex_outer_height (ρ : ℝ) (positive : 0 < ρ)
    (reflex : (net.patch 0).leftCorner = π + ρ) (x : Plane)
    (member : x ∈ (net.patch 0).hull) (nonzero : x ≠ 0) : 0 < det (direction (-ρ)) x := by
  have bound := net.first_reflex_bound ρ reflex
  have slit_pos := graph.curvature_pos small_faces (fanNeighbor source slit)
  have width := net.first_reflex_fan_width ρ reflex
  have at_left : 0 < det (direction (-ρ)) (net.patch 0).left := by
    rw [net.first_slit_position, det_smul_right, direction_det]
    exact mul_pos net.slitRadius_pos (sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
  have at_right : 0 < det (direction (-ρ)) (net.patch 0).right := by
    rw [net.patch_right]
    change 0 < det (direction (-ρ)) (_ • direction (graph.openingAngle (opposite source) slit 1))
    rw [det_smul_right, direction_det]
    exact mul_pos (graph.opening_radius_pos _ _ 1)
      (sin_pos_of_pos_of_lt_pi (by linarith [graph.openingAngle_nonneg (opposite source) slit 1]) (by linarith))
  have at_apex : 0 < det (direction (-ρ)) (net.patch 0).apex := by
    have expression : (net.patch 0).apex = (net.patch 0).left + ((net.patch 0).apex - (net.patch 0).left) := by module
    rw [expression, det_add_right, net.first_apex_direction_of_reflex ρ reflex, det_smul_right, det_self, mul_zero, add_zero]
    exact at_left
  apply radial_patch_height_pos (detHeight (direction (-ρ))).toLinearMap _ _ _ x at_left at_right at_apex _ nonzero
  simpa only [DevelopedPatch.hull, net.patch_pole] using member

theorem last_reflex_fan_width (ρ : ℝ) (reflex : (net.patch 3).rightCorner = π + ρ) :
    graph.totalAngleAt (opposite source) - graph.openingAngle (opposite source) slit 3 + ρ < π := by
  have total := angle_add_angle_add_angle_eq_pi (net.patch 3).left
    (ne₂₃_of_not_collinear (net.patch 3).fan_noncollinear)
  have petal_small := angle_lt_pi_of_not_collinear (net.patch 3).petal_noncollinear
  have other_nonnegative := angle_nonneg (net.patch 3).right (net.patch 3).left (net.patch 3).pole
  unfold DevelopedPatch.rightCorner at reflex
  have width_bound : angle (net.patch 3).left (net.patch 3).pole (net.patch 3).right + ρ < π := by linarith
  rw [net.patch_fan_pole_angle] at width_bound
  change graph.openingAngle (opposite source) slit 4 - graph.openingAngle (opposite source) slit 3 + ρ < π at width_bound
  rwa [graph.openingAngle_last] at width_bound

theorem last_reflex_outer_height (ρ : ℝ) (positive : 0 < ρ)
    (reflex : (net.patch 3).rightCorner = π + ρ) (x : Plane)
    (member : x ∈ (net.patch 3).hull) (nonzero : x ≠ 0) :
    det (direction (graph.totalAngleAt (opposite source) + ρ)) x < 0 := by
  let Γ := graph.totalAngleAt (opposite source)
  have corner_sum := net.slit_corner_sum
  rw [reflex] at corner_sum
  have corner_positive := (net.patch 0).leftCorner_pos
  have total_small := graph.totalAngleAt_lt_two_pi small_faces (fanNeighbor source slit)
  have ρ_small : ρ < π := by linarith
  have width := net.last_reflex_fan_width ρ reflex
  have at_right : det (direction (Γ + ρ)) (net.patch 3).right < 0 := by
    rw [net.last_slit_position_total, det_smul_right, direction_det]
    exact mul_neg_of_pos_of_neg net.slitRadius_pos
      (sin_neg_of_neg_of_neg_pi_lt (by dsimp [Γ]; linarith) (by dsimp [Γ]; linarith))
  have at_left : det (direction (Γ + ρ)) (net.patch 3).left < 0 := by
    rw [net.patch_left]
    change det (direction (Γ + ρ)) (_ • direction (graph.openingAngle (opposite source) slit 3)) < 0
    rw [det_smul_right, direction_det]
    apply mul_neg_of_pos_of_neg (graph.opening_radius_pos _ _ 3)
    apply sin_neg_of_neg_of_neg_pi_lt <;> dsimp [Γ] <;>
      linarith [graph.openingAngle_le_total (opposite source) slit 3]
  have at_apex : det (direction (Γ + ρ)) (net.patch 3).apex < 0 := by
    have vector := net.patch_apex_direction_right 3
    change (net.patch 3).apex - (net.patch 3).right = _ • direction
      (graph.openingAngle (opposite source) slit 4 - π + (net.patch 3).rightCorner) at vector
    rw [graph.openingAngle_last, reflex, show graph.totalAngleAt (opposite source) - π + (π + ρ) = Γ + ρ by dsimp [Γ]; ring] at vector
    have expression : (net.patch 3).apex = (net.patch 3).right + ((net.patch 3).apex - (net.patch 3).right) := by module
    rw [expression, det_add_right, vector, det_smul_right, det_self, mul_zero, add_zero]
    exact at_right
  have height := radial_patch_height_pos (-detHeight (direction (Γ + ρ))).toLinearMap _ _ _ x
    (by change 0 < -det (direction (Γ + ρ)) (net.patch 3).left; linarith)
    (by change 0 < -det (direction (Γ + ρ)) (net.patch 3).right; linarith)
    (by change 0 < -det (direction (Γ + ρ)) (net.patch 3).apex; linarith)
    (by simpa only [DevelopedPatch.hull, net.patch_pole] using member) nonzero
  change 0 < -det (direction (Γ + ρ)) x at height
  linarith

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
