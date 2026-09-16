import SixVertexUnfolding.Geometry.OctahedralPatchDirections
import SixVertexUnfolding.Geometry.OctahedralContactProjection

/-! The gap between adjacent copied source edges is exactly the curvature at their common equator vertex. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open Real EuclideanGeometry OctahedralTriangles

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

theorem junction_corner_sum (i : Fin 3) : (net.patch i.castSucc).rightCorner + (net.patch i.succ).leftCorner =
    graph.totalAngleAt (fanNeighbor source ((slit + i.castSucc) + 1)) := by
  have total := net.junction_angle_sum i
  rw [Fin.sum_univ_four] at total
  change angle (net.patch i.castSucc).apex (net.patch i.castSucc).right (net.patch i.castSucc).left +
    angle (net.patch i.castSucc).left (net.patch i.castSucc).right (net.patch i.castSucc).pole +
    angle (net.patch i.castSucc).pole (net.patch i.castSucc).right (net.patch i.succ).right +
    angle (net.patch i.succ).right (net.patch i.castSucc).right (net.patch i.succ).apex = _ at total
  unfold DevelopedPatch.rightCorner DevelopedPatch.leftCorner
  have same_pole : (net.patch i.succ).pole = (net.patch i.castSucc).pole := by rw [net.patch_pole, net.patch_pole]
  rw [← net.consecutive_patch_corner, same_pole,
    angle_comm (net.patch i.castSucc).pole (net.patch i.castSucc).right (net.patch i.castSucc).left,
    angle_comm (net.patch i.castSucc).left (net.patch i.castSucc).right (net.patch i.castSucc).apex]
  linarith

/-- The actual two polar direction formulas differ by the actual angular deficit. -/
theorem junction_direction_gap (i : Fin 3) :
    (graph.openingAngle (opposite source) slit i.succ.castSucc + π - (net.patch i.succ).leftCorner) -
      (graph.openingAngle (opposite source) slit i.castSucc.succ - π + (net.patch i.castSucc).rightCorner) =
        graph.curvature (fanNeighbor source ((slit + i.castSucc) + 1)) := by
  have total := net.junction_corner_sum i
  have same : i.succ.castSucc = i.castSucc.succ := rfl
  rw [same]
  unfold curvature
  linarith

/-- The signed area between adjacent copied edges is their common squared radius times the sine of the curvature gap. -/
theorem neighboring_apex_det (i : Fin 3) :
    det ((net.patch i.castSucc).apex - (net.patch i.castSucc).right)
      ((net.patch i.succ).apex - (net.patch i.castSucc).right) =
        dist (net.patch i.castSucc).apex (net.patch i.castSucc).right ^ 2 *
          sin (graph.curvature (fanNeighbor source ((slit + i.castSucc) + 1))) := by
  have next := net.patch_apex_direction_left i.succ
  rw [← net.consecutive_patch_corner, net.neighboring_apex_radii_equal] at next
  rw [net.patch_apex_direction_right, next, det_smul_left, det_smul_right, direction_det, net.junction_direction_gap]
  ring

/-- The dot product gives the cosine of that same actual curvature gap. -/
theorem neighboring_apex_inner (i : Fin 3) :
    inner ℝ ((net.patch i.castSucc).apex - (net.patch i.castSucc).right)
      ((net.patch i.succ).apex - (net.patch i.castSucc).right) =
        dist (net.patch i.castSucc).apex (net.patch i.castSucc).right ^ 2 *
          cos (graph.curvature (fanNeighbor source ((slit + i.castSucc) + 1))) := by
  have next := net.patch_apex_direction_left i.succ
  rw [← net.consecutive_patch_corner, net.neighboring_apex_radii_equal] at next
  rw [net.patch_apex_direction_right, next, real_inner_smul_left, inner_smul_right, direction_inner, net.junction_direction_gap]
  ring

theorem neighboring_apex_distance_sq (i : Fin 3) :
    dist (net.patch i.castSucc).apex (net.patch i.succ).apex ^ 2 =
      2 * dist (net.patch i.castSucc).apex (net.patch i.castSucc).right ^ 2 *
        (1 - cos (graph.curvature (fanNeighbor source ((slit + i.castSucc) + 1)))) := by
  have shifted : dist (net.patch i.castSucc).apex (net.patch i.succ).apex =
      dist ((net.patch i.castSucc).apex - (net.patch i.castSucc).right)
        ((net.patch i.succ).apex - (net.patch i.castSucc).right) := by
    simp only [dist_eq_norm]
    congr 1
    module
  rw [shifted]
  have next := net.patch_apex_direction_left i.succ
  rw [← net.consecutive_patch_corner, net.neighboring_apex_radii_equal] at next
  rw [net.patch_apex_direction_right, next, polar_distance_sq, net.junction_direction_gap]
  ring

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
