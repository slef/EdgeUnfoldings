import SixVertexUnfolding.Geometry.OctahedralPatchDirections

/-! The fan width and a reflex slit corner obey the original triangle angle sums. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open Real EuclideanGeometry OctahedralTriangles

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

theorem patch_fan_pole_angle (i : Fin 4) : angle (net.patch i).left (net.patch i).pole (net.patch i).right =
    graph.openingAngle (opposite source) slit i.succ - graph.openingAngle (opposite source) slit i.castSucc := by
  rw [net.patch_pole, net.patch_left, net.patch_right]
  apply radial_angle _ _ _ _ (graph.opening_radius_pos _ _ _) (graph.opening_radius_pos _ _ _)
  · rw [graph.openingAngle_step]; exact (graph.fanAngle_pos _ _).le
  · rw [graph.openingAngle_step]; exact (graph.fanAngle_lt_pi _ _).le

/-- A reflex first corner bounds the first fan width more strongly than a half-turn. -/
theorem first_reflex_fan_width (ρ : ℝ) (reflex : (net.patch 0).leftCorner = π + ρ) :
    graph.openingAngle (opposite source) slit 1 + ρ < π := by
  have left_ne_pole := ne₁₃_of_not_collinear (net.patch 0).fan_noncollinear
  have total := angle_add_angle_add_angle_eq_pi (net.patch 0).right left_ne_pole
  have petal_noncollinear : ¬ Collinear ℝ ({(net.patch 0).right, (net.patch 0).left, (net.patch 0).apex} : Set Plane) := by
    rw [Set.insert_comm]
    exact (net.patch 0).petal_noncollinear
  have petal_small := angle_lt_pi_of_not_collinear petal_noncollinear
  have other_nonnegative := angle_nonneg (net.patch 0).left (net.patch 0).right (net.patch 0).pole
  unfold DevelopedPatch.leftCorner at reflex
  rw [angle_comm (net.patch 0).right (net.patch 0).pole (net.patch 0).left] at total
  have width_bound : angle (net.patch 0).left (net.patch 0).pole (net.patch 0).right + ρ < π := by linarith
  rw [net.patch_fan_pole_angle] at width_bound
  change graph.openingAngle (opposite source) slit 1 - 0 + ρ < π at width_bound
  simpa only [sub_zero] using width_bound

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
