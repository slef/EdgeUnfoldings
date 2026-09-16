import SixVertexUnfolding.Geometry.TriangleFrame
import SixVertexUnfolding.Geometry.PetalCutHalfplane
import SixVertexUnfolding.Geometry.OctahedralApexGap

/-! A common upper frame for a middle petal and its two neighboring copies of the source vertex. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open Real EuclideanGeometry OctahedralTriangles

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

theorem patch_petal_area_neg (i : Fin 4) :
    det ((net.patch i).right - (net.patch i).left) ((net.patch i).apex - (net.patch i).left) < 0 := by
  have fan := net.patch_fan_area_pos i
  have nonzero := det_ne_zero_of_noncollinear _ _ _ (net.patch i).petal_noncollinear
  have outward := (oppositeHingeSides_iff_det _ _ _ _
    (ne₁₂_of_not_collinear (net.patch i).petal_noncollinear)).mp (net.patch i).outward
  by_contra nonnegative
  have positive := lt_of_le_of_ne (le_of_not_gt nonnegative) (Ne.symm nonzero)
  have impossible := mul_pos fan positive
  linarith

/-- Every petal lies below its oriented base, so putting it above the base reverses orientation. -/
theorem upper_patch_frame_reverses (i : Fin 4) (motion : Plane ≃ᵃⁱ[ℝ] Plane)
    (first : motion (net.patch i).left = 0)
    (second : motion (net.patch i).right = dist (net.patch i).left (net.patch i).right • direction 0)
    (apex : motion (net.patch i).apex = dist (net.patch i).left (net.patch i).apex •
      direction (angle (net.patch i).right (net.patch i).left (net.patch i).apex)) :
    ∀ x y : Plane, det (motion.linearIsometryEquiv x) (motion.linearIsometryEquiv y) = -det x y := by
  apply isometry_det_reverses motion.linearIsometryEquiv
    ((net.patch i).right - (net.patch i).left) ((net.patch i).apex - (net.patch i).left)
    (net.patch_petal_area_neg i)
  have displacement (p q : Plane) : motion.linearIsometryEquiv (p - q) = motion p - motion q :=
    motion.map_vsub p q
  rw [displacement, displacement, first, second, apex, sub_zero, sub_zero,
    det_smul_left, det_smul_right, direction_det, sub_zero]
  have reordered : ¬ Collinear ℝ ({(net.patch i).right, (net.patch i).left, (net.patch i).apex} : Set Plane) := by
    simpa only [Set.insert_comm] using (net.patch i).petal_noncollinear
  exact mul_pos (dist_pos.mpr (ne₁₂_of_not_collinear (net.patch i).petal_noncollinear))
    (mul_pos (dist_pos.mpr (ne₁₃_of_not_collinear (net.patch i).petal_noncollinear))
      (sin_pos_of_pos_of_lt_pi (angle_pos_of_not_collinear reordered) (angle_lt_pi_of_not_collinear reordered)))

/-- In any reversed frame, the previous apex is obtained by adding the common vertex's curvature. -/
theorem previous_apex_in_reversed_frame (i : Fin 3) (motion : Plane ≃ᵃⁱ[ℝ] Plane)
    (reverses : ∀ x y : Plane, det (motion.linearIsometryEquiv x) (motion.linearIsometryEquiv y) = -det x y)
    (φ : ℝ) (middle : motion (net.patch i.succ).apex - motion (net.patch i.castSucc).right =
      dist (net.patch i.castSucc).apex (net.patch i.castSucc).right • direction φ) :
    motion (net.patch i.castSucc).apex - motion (net.patch i.castSucc).right =
      dist (net.patch i.castSucc).apex (net.patch i.castSucc).right •
        direction (φ + graph.curvature (fanNeighbor source ((slit + i.castSucc) + 1))) := by
  have displacement (p q : Plane) : motion p - motion q = motion.linearIsometryEquiv (p - q) :=
    (motion.map_vsub p q).symm
  apply polar_point_eq_of_inner_det _ φ _ (dist_pos.mpr (net.petal_apex_ne_right i.castSucc))
  · rw [← middle, displacement, displacement, motion.linearIsometryEquiv.inner_map_map, real_inner_comm]
    exact net.neighboring_apex_inner i
  · rw [← middle, displacement, displacement, reverses, det_swap, neg_neg]
    exact net.neighboring_apex_det i

/-- In the same reversed frame, the next apex is obtained by subtracting its common vertex's curvature. -/
theorem next_apex_in_reversed_frame (i : Fin 3) (motion : Plane ≃ᵃⁱ[ℝ] Plane)
    (reverses : ∀ x y : Plane, det (motion.linearIsometryEquiv x) (motion.linearIsometryEquiv y) = -det x y)
    (φ : ℝ) (middle : motion (net.patch i.castSucc).apex - motion (net.patch i.castSucc).right =
      dist (net.patch i.castSucc).apex (net.patch i.castSucc).right • direction φ) :
    motion (net.patch i.succ).apex - motion (net.patch i.castSucc).right =
      dist (net.patch i.castSucc).apex (net.patch i.castSucc).right •
        direction (φ - graph.curvature (fanNeighbor source ((slit + i.castSucc) + 1))) := by
  have displacement (p q : Plane) : motion p - motion q = motion.linearIsometryEquiv (p - q) :=
    (motion.map_vsub p q).symm
  change _ = _ • direction (φ + -graph.curvature _)
  apply polar_point_eq_of_inner_det _ φ _ (dist_pos.mpr (net.petal_apex_ne_right i.castSucc))
  · rw [← middle, displacement, displacement, motion.linearIsometryEquiv.inner_map_map, cos_neg]
    exact net.neighboring_apex_inner i
  · rw [← middle, displacement, displacement, reverses, net.neighboring_apex_det, sin_neg]
    ring

/-- The previous source copy is the middle triangle's left ray widened by the actual curvature. -/
theorem previous_apex_in_upper_frame (i : Fin 3) (motion : Plane ≃ᵃⁱ[ℝ] Plane)
    (first : motion (net.patch i.succ).left = 0)
    (second : motion (net.patch i.succ).right = dist (net.patch i.succ).left (net.patch i.succ).right • direction 0)
    (apex : motion (net.patch i.succ).apex = dist (net.patch i.succ).left (net.patch i.succ).apex •
      direction (angle (net.patch i.succ).right (net.patch i.succ).left (net.patch i.succ).apex)) :
    motion (net.patch i.castSucc).apex = dist (net.patch i.succ).left (net.patch i.succ).apex •
      direction (angle (net.patch i.succ).right (net.patch i.succ).left (net.patch i.succ).apex +
        graph.curvature (fanNeighbor source ((slit + i.castSucc) + 1))) := by
  have shared : motion (net.patch i.castSucc).right = 0 := by rw [net.consecutive_patch_corner, first]
  have radius : dist (net.patch i.castSucc).apex (net.patch i.castSucc).right =
      dist (net.patch i.succ).left (net.patch i.succ).apex := by
    rw [← net.neighboring_apex_radii_equal, net.consecutive_patch_corner, dist_comm]
  have previous := net.previous_apex_in_reversed_frame i motion
    (net.upper_patch_frame_reverses i.succ motion first second apex)
    (angle (net.patch i.succ).right (net.patch i.succ).left (net.patch i.succ).apex)
    (by rw [shared, sub_zero, radius]; exact apex)
  simpa only [shared, sub_zero, radius] using previous

theorem next_apex_in_upper_frame (i : Fin 3) (motion : Plane ≃ᵃⁱ[ℝ] Plane)
    (first : motion (net.patch i.castSucc).left = 0)
    (second : motion (net.patch i.castSucc).right = dist (net.patch i.castSucc).left (net.patch i.castSucc).right • direction 0)
    (apex : motion (net.patch i.castSucc).apex = dist (net.patch i.castSucc).left (net.patch i.castSucc).apex •
      direction (angle (net.patch i.castSucc).right (net.patch i.castSucc).left (net.patch i.castSucc).apex)) :
    motion (net.patch i.succ).apex = dist (net.patch i.castSucc).left (net.patch i.castSucc).right • direction 0 +
      dist (net.patch i.castSucc).right (net.patch i.castSucc).apex •
        direction (π - angle (net.patch i.castSucc).left (net.patch i.castSucc).right (net.patch i.castSucc).apex -
          graph.curvature (fanNeighbor source ((slit + i.castSucc) + 1))) := by
  have middle := upper_triangle_frame_right _ _ _ (net.patch i.castSucc).petal_noncollinear motion first second apex
  have radius : dist (net.patch i.castSucc).apex (net.patch i.castSucc).right =
      dist (net.patch i.castSucc).right (net.patch i.castSucc).apex := dist_comm _ _
  have next := net.next_apex_in_reversed_frame i motion
    (net.upper_patch_frame_reverses i.castSucc motion first second apex)
    (π - angle (net.patch i.castSucc).left (net.patch i.castSucc).right (net.patch i.castSucc).apex)
    (by rw [middle, second, radius]; module)
  rw [second, radius] at next
  exact (sub_eq_iff_eq_add.mp next).trans (add_comm _ _)

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
