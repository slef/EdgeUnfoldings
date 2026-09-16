import SixVertexUnfolding.Geometry.OctahedralBaseCones
import SixVertexUnfolding.Geometry.PocketHeight

/-! The first geometric step of the small-fan pocket argument, for the actual developed petals. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open Real EuclideanGeometry OctahedralTriangles

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

/-- Every meeting of the two closed outer petals lies strictly below the middle base. -/
theorem opposite_contact_below_base (i : Fin 2) (motion : Plane ≃ᵃⁱ[ℝ] Plane)
    (first : motion (net.patch i.castSucc.succ).left = 0)
    (second : motion (net.patch i.castSucc.succ).right =
      dist (net.patch i.castSucc.succ).left (net.patch i.castSucc.succ).right • direction 0)
    (apex : motion (net.patch i.castSucc.succ).apex =
      dist (net.patch i.castSucc.succ).left (net.patch i.castSucc.succ).apex •
        direction (angle (net.patch i.castSucc.succ).right (net.patch i.castSucc.succ).left (net.patch i.castSucc.succ).apex))
    (small : net.leftFanCorner i + net.rightFanCorner i < π)
    (x : Plane) (left : x ∈ net.placedTriangle (true, i.castSucc.castSucc))
    (right : x ∈ net.placedTriangle (true, i.succ.succ)) : (motion x) 1 < 0 := by
  have cones := net.opposite_petals_in_base_cones i motion first second apex
  have left_bounds := net.left_base_cone_bounds i
  have right_bounds := net.right_base_cone_bounds i
  exact base_cones_pocket_below _ _ _ _ _
    (dist_pos.mpr (ne₁₂_of_not_collinear (net.patch i.castSucc.succ).petal_noncollinear))
    (net.leftFanCorner_pos i) (net.rightFanCorner_pos i) small
    ⟨left_bounds.1.le, left_bounds.2.le⟩ ⟨right_bounds.1.le, right_bounds.2.le⟩
    (motion x) (cones.1 (Set.mem_image_of_mem motion left)) (cones.2 (Set.mem_image_of_mem motion right))

/-- The other three vertices of the proposed pocket also lie strictly below the base. -/
theorem pocket_corners_below_base (i : Fin 2) (motion : Plane ≃ᵃⁱ[ℝ] Plane)
    (first : motion (net.patch i.castSucc.succ).left = 0)
    (second : motion (net.patch i.castSucc.succ).right =
      dist (net.patch i.castSucc.succ).left (net.patch i.castSucc.succ).right • direction 0)
    (apex : motion (net.patch i.castSucc.succ).apex =
      dist (net.patch i.castSucc.succ).left (net.patch i.castSucc.succ).apex •
        direction (angle (net.patch i.castSucc.succ).right (net.patch i.castSucc.succ).left (net.patch i.castSucc.succ).apex))
    (small : net.leftFanCorner i + net.rightFanCorner i < π) :
    (motion (net.patch i.castSucc.castSucc).left) 1 < 0 ∧
      (motion (net.patch i.succ.succ).right) 1 < 0 ∧ (motion 0) 1 < 0 := by
  have σ_pos := net.leftFanCorner_pos i
  have τ_pos := net.rightFanCorner_pos i
  have sine_σ := sin_pos_of_pos_of_lt_pi σ_pos (show net.leftFanCorner i < π by linarith)
  have sine_τ := sin_pos_of_pos_of_lt_pi τ_pos (show net.rightFanCorner i < π by linarith)
  have left := net.previous_base_ray_in_upper_frame i motion first second apex
  have right := net.next_base_ray_in_upper_frame i motion first second apex
  have left_length : 0 < dist (net.patch i.castSucc.castSucc).right (net.patch i.castSucc.castSucc).left :=
    dist_pos.mpr (ne₁₂_of_not_collinear (net.patch i.castSucc.castSucc).petal_noncollinear).symm
  have right_length : 0 < dist (net.patch i.succ.succ).left (net.patch i.succ.succ).right :=
    dist_pos.mpr (ne₁₂_of_not_collinear (net.patch i.succ.succ).petal_noncollinear)
  have shared : motion (net.patch i.succ.succ).left =
      dist (net.patch i.castSucc.succ).left (net.patch i.castSucc.succ).right • direction 0 := by
    rw [← net.consecutive_patch_corner i.succ]
    exact second
  refine ⟨?_, ?_, ?_⟩
  · rw [left, direction_two_pi_sub]
    simp only [PiLp.smul_apply, smul_eq_mul, direction_y, sin_neg]
    exact mul_neg_of_pos_of_neg left_length (neg_neg_of_pos sine_σ)
  · have coordinate := congrArg (fun p : Plane => p 1) right
    rw [shared] at coordinate
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, direction_y, sin_zero,
      mul_zero, sub_zero, sin_sub_pi] at coordinate
    rw [coordinate]
    exact mul_neg_of_pos_of_neg right_length (neg_neg_of_pos sine_τ)
  · have reverses := net.upper_patch_frame_reverses i.castSucc.succ motion first second apex
    have area := net.patch_fan_area_pos i.castSucc.succ
    have displacement (p q : Plane) : motion p - motion q = motion.linearIsometryEquiv (p - q) :=
      (motion.map_vsub p q).symm
    have negative : det (motion (net.patch i.castSucc.succ).right - motion (net.patch i.castSucc.succ).left)
        (motion (net.patch i.castSucc.succ).pole - motion (net.patch i.castSucc.succ).left) < 0 := by
      rw [displacement, displacement, reverses]
      exact neg_neg_of_pos area
    rw [first, second, net.patch_pole, sub_zero, sub_zero, det_smul_left] at negative
    simp only [det, direction_x, direction_y, cos_zero, sin_zero, one_mul, zero_mul, sub_zero] at negative
    have length_pos := dist_pos.mpr (ne₁₂_of_not_collinear (net.patch i.castSucc.succ).petal_noncollinear)
    nlinarith

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
