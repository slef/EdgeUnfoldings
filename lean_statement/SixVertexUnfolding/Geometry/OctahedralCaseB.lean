import SixVertexUnfolding.Geometry.OctahedralBaseCones
import SixVertexUnfolding.Geometry.BaseConeSeparation

/-! The base-cone case separates actual opposite petals, including both equality boundaries. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open Real EuclideanGeometry OctahedralTriangles

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

/-- If both opposite angle sums are at least pi, the two whole closed petals lie in disjoint base cones. -/
theorem opposite_petals_caseB (i : Fin 2)
    (outer_wide : π ≤ net.widenedLeft i + net.widenedRight i)
    (fan_wide : π ≤ net.leftFanCorner i + net.rightFanCorner i) :
    Disjoint (net.placedTriangle (true, i.castSucc.castSucc)) (net.placedTriangle (true, i.succ.succ)) := by
  let middle := net.patch i.castSucc.succ
  let base := dist middle.left middle.right
  let α := net.widenedLeft i
  let β := net.widenedRight i
  let σ := net.leftFanCorner i
  let τ := net.rightFanCorner i
  have base_pos : 0 < base := dist_pos.mpr (ne₁₂_of_not_collinear middle.petal_noncollinear)
  have α_pos : 0 < α := add_pos_of_nonneg_of_pos (angle_nonneg _ _ _)
    (graph.curvature_pos small_faces _)
  have β_pos : 0 < β := add_pos_of_nonneg_of_pos (angle_nonneg _ _ _)
    (graph.curvature_pos small_faces _)
  have left_bounds := net.left_base_cone_bounds i
  have right_bounds := net.right_base_cone_bounds i
  have cones := base_cones_disjoint base α β σ τ base_pos α_pos β_pos
    (net.leftFanCorner_pos i) (net.rightFanCorner_pos i) left_bounds.2.le right_bounds.2.le
    left_bounds.1.le right_bounds.1.le outer_wide fan_wide
  obtain ⟨motion, first, second, apex⟩ := exists_upper_triangle_frame middle.left middle.right middle.apex middle.petal_noncollinear
  obtain ⟨left_contained, right_contained⟩ := net.opposite_petals_in_base_cones i motion first second apex
  rw [direction_sub_pi] at right_contained
  have right_ray : direction (π - β) = -direction (2 * π - β) := by
    rw [show 2 * π - β = (π - β) + π by ring, direction_add_pi, neg_neg]
  rw [right_ray] at right_contained
  exact (Set.disjoint_image_iff motion.injective).mp (cones.mono left_contained right_contained)

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
