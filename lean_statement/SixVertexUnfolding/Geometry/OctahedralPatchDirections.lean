import SixVertexUnfolding.Geometry.OctahedralDevelopment
import SixVertexUnfolding.Geometry.OctahedralPatchCorners
import SixVertexUnfolding.Geometry.OctahedralFanHinges
import SixVertexUnfolding.Geometry.OutwardPolarDirections

/-! The actual copied-apex directions are the cumulative fan direction plus the appropriate patch corner. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open EuclideanGeometry Real OctahedralTriangles

namespace DevelopedPatch

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph} {source : Fin 6} {sector : Fin 4}

/-- The two face angles at the patch's first equator endpoint; their sum may be reflex. -/
noncomputable def leftCorner (patch : graph.DevelopedPatch source sector) : ℝ :=
  angle patch.pole patch.left patch.right + angle patch.right patch.left patch.apex

/-- The corresponding corner at the patch's last equator endpoint. -/
noncomputable def rightCorner (patch : graph.DevelopedPatch source sector) : ℝ :=
  angle patch.pole patch.right patch.left + angle patch.left patch.right patch.apex

theorem leftCorner_pos (patch : graph.DevelopedPatch source sector) : 0 < patch.leftCorner := by
  have petal : ¬ Collinear ℝ ({patch.right, patch.left, patch.apex} : Set Plane) := by
    rw [Set.insert_comm]
    exact patch.petal_noncollinear
  have positive := angle_pos_of_not_collinear petal
  have nonnegative := angle_nonneg patch.pole patch.left patch.right
  unfold leftCorner
  linarith

theorem rightCorner_pos (patch : graph.DevelopedPatch source sector) : 0 < patch.rightCorner := by
  have positive := angle_pos_of_not_collinear patch.petal_noncollinear
  have nonnegative := angle_nonneg patch.pole patch.right patch.left
  unfold rightCorner
  linarith

end DevelopedPatch

namespace Development

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

/-- Exact direction of the copied cut edge at the first endpoint of any actual patch. -/
theorem patch_apex_direction_left (i : Fin 4) :
    (net.patch i).apex - (net.patch i).left = dist (net.patch i).apex (net.patch i).left •
      direction (graph.openingAngle (opposite source) slit i.castSucc + π - (net.patch i).leftCorner) := by
  have noncollinear := (net.patch i).petal_noncollinear
  have outward := (net.patch i).outward
  rw [net.patch_left, net.patch_right] at noncollinear
  rw [net.patch_left, net.patch_right, net.patch_pole] at outward
  unfold DevelopedPatch.leftCorner
  rw [net.patch_left, net.patch_right, net.patch_pole]
  apply outward_petal_direction_left _ _ _ _ (graph.opening_radius_pos _ _ _) (graph.opening_radius_pos _ _ _)
  · rw [graph.openingAngle_step]; exact graph.fanAngle_pos _ _
  · rw [graph.openingAngle_step]; exact graph.fanAngle_lt_pi _ _
  · exact noncollinear
  · exact outward

/-- Exact direction of the copied cut edge at the last endpoint of any actual patch. -/
theorem patch_apex_direction_right (i : Fin 4) :
    (net.patch i).apex - (net.patch i).right = dist (net.patch i).apex (net.patch i).right •
      direction (graph.openingAngle (opposite source) slit i.succ - π + (net.patch i).rightCorner) := by
  have noncollinear := (net.patch i).petal_noncollinear
  have outward := (net.patch i).outward
  rw [net.patch_left, net.patch_right] at noncollinear
  rw [net.patch_left, net.patch_right, net.patch_pole] at outward
  unfold DevelopedPatch.rightCorner
  rw [net.patch_left, net.patch_right, net.patch_pole]
  apply outward_petal_direction_right _ _ _ _ (graph.opening_radius_pos _ _ _) (graph.opening_radius_pos _ _ _)
  · rw [graph.openingAngle_step]; exact graph.fanAngle_pos _ _
  · rw [graph.openingAngle_step]; exact graph.fanAngle_lt_pi _ _
  · exact noncollinear
  · exact outward

theorem patch_base_direction_left (i : Fin 4) :
    (net.patch i).right - (net.patch i).left = dist (net.patch i).left (net.patch i).right •
      direction (graph.openingAngle (opposite source) slit i.castSucc + π -
        angle 0 (net.patch i).left (net.patch i).right) := by
  rw [net.patch_left, net.patch_right]
  apply radial_base_direction_left _ _ _ _ (graph.opening_radius_pos _ _ _) (graph.opening_radius_pos _ _ _)
  · rw [graph.openingAngle_step]; exact graph.fanAngle_pos _ _
  · rw [graph.openingAngle_step]; exact graph.fanAngle_lt_pi _ _

theorem patch_base_direction_right (i : Fin 4) :
    (net.patch i).left - (net.patch i).right = dist (net.patch i).left (net.patch i).right •
      direction (graph.openingAngle (opposite source) slit i.succ - π +
        angle 0 (net.patch i).right (net.patch i).left) := by
  rw [net.patch_left, net.patch_right]
  apply radial_base_direction_right _ _ _ _ (graph.opening_radius_pos _ _ _) (graph.opening_radius_pos _ _ _)
  · rw [graph.openingAngle_step]; exact graph.fanAngle_pos _ _
  · rw [graph.openingAngle_step]; exact graph.fanAngle_lt_pi _ _

end Development
end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
