import SixVertexUnfolding.Geometry.OctahedralBaseRays

/-! Both actual outer petals lie in the base cones used by the large-fan and pocket arguments. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open Real EuclideanGeometry OctahedralTriangles

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

/-- This common pair of cone containments makes no assumption on which angle case holds. -/
theorem opposite_petals_in_base_cones (i : Fin 2) (motion : Plane ≃ᵃⁱ[ℝ] Plane)
    (first : motion (net.patch i.castSucc.succ).left = 0)
    (second : motion (net.patch i.castSucc.succ).right =
      dist (net.patch i.castSucc.succ).left (net.patch i.castSucc.succ).right • direction 0)
    (apex : motion (net.patch i.castSucc.succ).apex =
      dist (net.patch i.castSucc.succ).left (net.patch i.castSucc.succ).apex •
        direction (angle (net.patch i.castSucc.succ).right (net.patch i.castSucc.succ).left (net.patch i.castSucc.succ).apex)) :
    (motion '' net.placedTriangle (true, i.castSucc.castSucc) ⊆
      translatedCone 0 (direction (net.widenedLeft i)) (direction (2 * π - net.leftFanCorner i))) ∧
    (motion '' net.placedTriangle (true, i.succ.succ) ⊆
      translatedCone (dist (net.patch i.castSucc.succ).left (net.patch i.castSucc.succ).right • direction 0)
        (direction (net.rightFanCorner i - π)) (direction (π - net.widenedRight i))) := by
  let previous := net.patch i.castSucc.castSucc
  let middle := net.patch i.castSucc.succ
  let next := net.patch i.succ.succ
  let base := dist middle.left middle.right
  let s := dist middle.left middle.apex
  let t := dist middle.right middle.apex
  let α := net.widenedLeft i
  let β := net.widenedRight i
  let σ := net.leftFanCorner i
  let τ := net.rightFanCorner i
  have at_previous := net.previous_apex_in_upper_frame i.castSucc motion first second apex
  change motion previous.apex = s • direction α at at_previous
  have at_left := net.previous_base_ray_in_upper_frame i motion first second apex
  change motion previous.left = dist previous.right previous.left • direction (2 * π - σ) at at_left
  have previous_shared : motion previous.right = 0 := by
    change motion (net.patch i.castSucc.castSucc).right = 0
    rw [net.consecutive_patch_corner]
    exact first
  have at_next := net.next_apex_in_upper_frame i.succ motion first second apex
  rw [show i.succ.castSucc = i.castSucc.succ from rfl] at at_next
  change motion next.apex = base • direction 0 + t • direction
    (π - angle middle.left middle.right middle.apex - graph.curvature (fanNeighbor source ((slit + i.castSucc.succ) + 1))) at at_next
  have angle_eq : π - angle middle.left middle.right middle.apex -
      graph.curvature (fanNeighbor source ((slit + i.castSucc.succ) + 1)) = π - β := by
    dsimp [β, widenedRight]
    ring
  rw [angle_eq] at at_next
  have at_right := net.next_base_ray_in_upper_frame i motion first second apex
  change motion next.right - motion next.left = dist next.left next.right • direction (τ - π) at at_right
  have next_shared : motion next.left = base • direction 0 := by
    change motion (net.patch i.succ.succ).left = _
    rw [← net.consecutive_patch_corner i.succ]
    exact second
  constructor
  · rw [net.placed_petal_image]
    apply convexHull_min _ (translatedCone_convex _ _ _)
    rintro x (rfl | rfl | rfl)
    · change motion previous.left - 0 ∈ twoRayCone (direction α) (direction (2 * π - σ))
      rw [sub_zero, at_left]
      exact ⟨0, dist previous.right previous.left, le_rfl, dist_nonneg, by simp⟩
    · change motion previous.right - 0 ∈ twoRayCone _ _
      rw [previous_shared, sub_self]
      exact zero_mem_twoRayCone _ _
    · change motion previous.apex - 0 ∈ twoRayCone (direction α) (direction (2 * π - σ))
      rw [sub_zero, at_previous]
      exact ⟨s, 0, dist_nonneg, le_rfl, by simp⟩
  · rw [net.placed_petal_image]
    apply convexHull_min _ (translatedCone_convex _ _ _)
    rintro x (rfl | rfl | rfl)
    · change motion next.left - base • direction 0 ∈ twoRayCone _ _
      rw [next_shared, sub_self]
      exact zero_mem_twoRayCone _ _
    · change motion next.right - base • direction 0 ∈ twoRayCone (direction (τ - π)) (direction (π - β))
      rw [← next_shared, at_right]
      exact ⟨dist next.left next.right, 0, dist_nonneg, le_rfl, by simp⟩
    · change motion next.apex - base • direction 0 ∈ twoRayCone (direction (τ - π)) (direction (π - β))
      rw [at_next, add_sub_cancel_left]
      exact ⟨0, t, le_rfl, dist_nonneg, by simp⟩

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
