import SixVertexUnfolding.Geometry.OctahedralBaseAngles

/-! Exact outer equator rays in the common upper frame of an opposite-petal comparison. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open Real EuclideanGeometry

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

/-- The previous equator corner has direction minus the sum of its two intervening fan angles. -/
theorem previous_base_ray_in_upper_frame (i : Fin 2) (motion : Plane ≃ᵃⁱ[ℝ] Plane)
    (first : motion (net.patch i.castSucc.succ).left = 0)
    (second : motion (net.patch i.castSucc.succ).right =
      dist (net.patch i.castSucc.succ).left (net.patch i.castSucc.succ).right • direction 0)
    (apex : motion (net.patch i.castSucc.succ).apex =
      dist (net.patch i.castSucc.succ).left (net.patch i.castSucc.succ).apex •
        direction (angle (net.patch i.castSucc.succ).right (net.patch i.castSucc.succ).left (net.patch i.castSucc.succ).apex)) :
    motion (net.patch i.castSucc.castSucc).left =
      dist (net.patch i.castSucc.castSucc).right (net.patch i.castSucc.castSucc).left • direction (2 * π - net.leftFanCorner i) := by
  let previous := net.patch i.castSucc.castSucc
  let middle := net.patch i.castSucc.succ
  let s := dist middle.left middle.apex
  let α := net.widenedLeft i
  let σ := net.leftFanCorner i
  have reverses := net.upper_patch_frame_reverses i.castSucc.succ motion first second apex
  have at_previous := net.previous_apex_in_upper_frame i.castSucc motion first second apex
  change motion previous.apex = s • direction α at at_previous
  have shared : motion previous.right = 0 := by
    change motion (net.patch i.castSucc.castSucc).right = 0
    rw [net.consecutive_patch_corner]
    exact first
  have measured (p q r : Plane) : angle (motion p) (motion q) (motion r) = angle p q r :=
    motion.toAffineIsometry.angle_map p q r
  have displacement (p q : Plane) : motion p - motion q = motion.linearIsometryEquiv (p - q) :=
    (motion.map_vsub p q).symm
  have noncollinear : ¬ Collinear ℝ ({previous.apex, previous.right, previous.left} : Set Plane) := by
    have reorder : ({previous.apex, previous.right, previous.left} : Set Plane) = {previous.left, previous.right, previous.apex} := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [reorder]
    exact previous.petal_noncollinear
  have corner : angle (motion previous.apex) (motion previous.right) (motion previous.left) = 2 * π - σ - α := by
    rw [measured, angle_comm]
    have total := net.left_base_angle_sum i
    change α + σ + angle previous.left previous.right previous.apex = 2 * π at total
    linarith
  have vector := counterclockwise_corner_vector (motion previous.right) (motion previous.apex) (motion previous.left) s α
    (dist_pos.mpr (ne₁₃_of_not_collinear middle.petal_noncollinear))
    (by rw [motion.dist_map]; exact dist_pos.mpr (ne₂₃_of_not_collinear noncollinear))
    (by rw [measured]; exact angle_pos_of_not_collinear noncollinear)
    (by rw [measured]; exact angle_lt_pi_of_not_collinear noncollinear)
    (by rw [at_previous, shared, sub_zero])
    (by
      rw [displacement, displacement, reverses,
        det_triangle_cyclic previous.apex previous.left previous.right,
        det_triangle_cyclic previous.left previous.right previous.apex]
      exact neg_nonneg.mpr (net.patch_petal_area_neg i.castSucc.castSucc).le)
  rw [corner, motion.dist_map, shared, sub_zero,
    show α + (2 * π - σ - α) = 2 * π - σ by ring] at vector
  exact vector

/-- The next equator corner has direction pi plus the corresponding fan-angle sum. -/
theorem next_base_ray_in_upper_frame (i : Fin 2) (motion : Plane ≃ᵃⁱ[ℝ] Plane)
    (first : motion (net.patch i.castSucc.succ).left = 0)
    (second : motion (net.patch i.castSucc.succ).right =
      dist (net.patch i.castSucc.succ).left (net.patch i.castSucc.succ).right • direction 0)
    (apex : motion (net.patch i.castSucc.succ).apex =
      dist (net.patch i.castSucc.succ).left (net.patch i.castSucc.succ).apex •
        direction (angle (net.patch i.castSucc.succ).right (net.patch i.castSucc.succ).left (net.patch i.castSucc.succ).apex)) :
    motion (net.patch i.succ.succ).right - motion (net.patch i.succ.succ).left =
      dist (net.patch i.succ.succ).left (net.patch i.succ.succ).right • direction (net.rightFanCorner i - π) := by
  let middle := net.patch i.castSucc.succ
  let next := net.patch i.succ.succ
  let base := dist middle.left middle.right
  let t := dist middle.right middle.apex
  let β := net.widenedRight i
  let τ := net.rightFanCorner i
  have reverses := net.upper_patch_frame_reverses i.castSucc.succ motion first second apex
  have at_next := net.next_apex_in_upper_frame i.succ motion first second apex
  rw [show i.succ.castSucc = i.castSucc.succ from rfl] at at_next
  change motion next.apex = base • direction 0 + t • direction (π -
    angle middle.left middle.right middle.apex - graph.curvature _) at at_next
  have right_direction : π - angle middle.left middle.right middle.apex -
      graph.curvature (OctahedralTriangles.fanNeighbor source ((slit + i.castSucc.succ) + 1)) = π - β := by
    dsimp [β, widenedRight]
    ring
  rw [right_direction] at at_next
  have shared : motion next.left = base • direction 0 := by
    change motion (net.patch i.succ.succ).left = _
    rw [← net.consecutive_patch_corner i.succ]
    exact second
  have measured (p q r : Plane) : angle (motion p) (motion q) (motion r) = angle p q r :=
    motion.toAffineIsometry.angle_map p q r
  have displacement (p q : Plane) : motion p - motion q = motion.linearIsometryEquiv (p - q) :=
    (motion.map_vsub p q).symm
  have noncollinear : ¬ Collinear ℝ ({next.apex, next.left, next.right} : Set Plane) := by
    have reorder : ({next.apex, next.left, next.right} : Set Plane) = {next.left, next.right, next.apex} := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [reorder]
    exact next.petal_noncollinear
  have corner : angle (motion next.apex) (motion next.left) (motion next.right) = 2 * π - τ - β := by
    rw [measured, angle_comm]
    have total := net.right_base_angle_sum i
    change β + τ + angle next.right next.left next.apex = 2 * π at total
    linarith
  have vector := clockwise_corner_vector (motion next.left) (motion next.apex) (motion next.right) t (π - β)
    (dist_pos.mpr (ne₂₃_of_not_collinear middle.petal_noncollinear))
    (by rw [motion.dist_map]; exact dist_pos.mpr (ne₂₃_of_not_collinear noncollinear))
    (by rw [measured]; exact angle_pos_of_not_collinear noncollinear)
    (by rw [measured]; exact angle_lt_pi_of_not_collinear noncollinear)
    (by rw [at_next, shared]; module)
    (by
      rw [displacement, displacement, reverses, det_swap, neg_neg]
      exact (net.patch_petal_area_neg i.succ.succ).le)
  rw [corner, motion.dist_map, show π - β - (2 * π - τ - β) = τ - π by ring] at vector
  exact vector

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
