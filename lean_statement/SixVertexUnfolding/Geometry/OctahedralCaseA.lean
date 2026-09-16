import SixVertexUnfolding.Geometry.OctahedralOppositeAngles
import SixVertexUnfolding.Geometry.CaseASeparation

/-! Case A separates the two actual opposite petals, in the same developed net. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open Real EuclideanGeometry OctahedralTriangles

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

/-- If the widened base angles total less than pi and contain both outer apex angles,
the entire two closed opposite petals are disjoint. All coordinates come from this net. -/
theorem opposite_petals_caseA (i : Fin 2)
    (narrow : net.widenedLeft i + net.widenedRight i < π)
    (left_fits : net.petalApexAngle i.castSucc.castSucc ≤ net.widenedLeft i + net.widenedRight i)
    (right_fits : net.petalApexAngle i.succ.succ ≤ net.widenedLeft i + net.widenedRight i) :
    Disjoint (net.placedTriangle (true, i.castSucc.castSucc)) (net.placedTriangle (true, i.succ.succ)) := by
  let previous := net.patch i.castSucc.castSucc
  let middle := net.patch i.castSucc.succ
  let next := net.patch i.succ.succ
  let base := dist middle.left middle.right
  let s := dist middle.left middle.apex
  let t := dist middle.right middle.apex
  let φ := angle middle.right middle.left middle.apex
  let ψ := angle middle.left middle.right middle.apex
  let α := net.widenedLeft i
  let β := net.widenedRight i
  have base_pos : 0 < base := dist_pos.mpr (ne₁₂_of_not_collinear middle.petal_noncollinear)
  have s_pos : 0 < s := dist_pos.mpr (ne₁₃_of_not_collinear middle.petal_noncollinear)
  have t_pos : 0 < t := dist_pos.mpr (ne₂₃_of_not_collinear middle.petal_noncollinear)
  have φ_pos : 0 < φ := by
    apply angle_pos_of_not_collinear
    simpa only [Set.insert_comm] using middle.petal_noncollinear
  have ψ_pos : 0 < ψ := angle_pos_of_not_collinear middle.petal_noncollinear
  have left_wider : φ < α := by
    have positive := graph.curvature_pos small_faces (fanNeighbor source ((slit + i.castSucc.castSucc) + 1))
    change φ < φ + _
    linarith
  have right_wider : ψ < β := by
    have positive := graph.curvature_pos small_faces (fanNeighbor source ((slit + i.castSucc.succ) + 1))
    change ψ < ψ + _
    linarith
  obtain ⟨motion, first, second, apex⟩ := exists_upper_triangle_frame middle.left middle.right middle.apex middle.petal_noncollinear
  have reverses := net.upper_patch_frame_reverses i.castSucc.succ motion first second apex
  have middle_right := upper_triangle_frame_right _ _ _ middle.petal_noncollinear motion first second apex
  have at_previous := net.previous_apex_in_upper_frame i.castSucc motion first second apex
  change motion previous.apex = s • direction α at at_previous
  have at_next := net.next_apex_in_upper_frame i.succ motion first second apex
  change motion next.apex = base • direction 0 + t • direction (π - ψ -
    graph.curvature (fanNeighbor source ((slit + i.castSucc.succ) + 1))) at at_next
  have right_direction : π - ψ - graph.curvature (fanNeighbor source ((slit + i.castSucc.succ) + 1)) = π - β := by
    change π - ψ - _ = π - (ψ + _)
    ring
  rw [right_direction] at at_next
  have cones := CutRays.caseA_opposed_apex_cones base s t α β φ ψ (motion middle.apex)
    base_pos s_pos t_pos φ_pos ψ_pos left_wider right_wider narrow apex middle_right
  have shared_left : motion previous.right = 0 := by
    change motion (net.patch i.castSucc.castSucc).right = 0
    rw [net.consecutive_patch_corner]
    exact first
  have shared_right : motion next.left = base • direction 0 := by
    change motion (net.patch i.succ.succ).left = _
    rw [← net.consecutive_patch_corner i.succ]
    exact second
  have left_edge : motion previous.right - motion previous.apex = s • direction (α + π) := by
    rw [shared_left, at_previous, direction_add_pi]
    module
  have right_edge : motion next.left - motion next.apex = t • direction (-β) := by
    have direction_eq : direction (π - β) = -direction (-β) := by
      rw [show π - β = -β + π by ring, direction_add_pi]
    rw [shared_right, at_next, direction_eq]
    module
  have left_contained := net.petal_image_in_clockwise_cone i.castSucc.castSucc motion reverses s (π - β) (α + π)
    s_pos left_edge (by rw [angle_comm]; change net.petalApexAngle _ ≤ _; linarith) (by linarith)
  have right_contained := net.petal_image_in_counterclockwise_cone i.succ.succ motion reverses t (-β) α
    t_pos right_edge (by change net.petalApexAngle _ ≤ _; linarith) (by linarith)
  have negative_right : -direction (π - β) = direction (-β) := by
    rw [show π - β = -β + π by ring, direction_add_pi, neg_neg]
  rw [at_previous, direction_add_pi] at left_contained
  rw [at_next] at right_contained
  have left_swap : translatedCone (s • direction α) (direction (π - β)) (-direction α) =
      translatedCone (s • direction α) (-direction α) (direction (π - β)) := by
    unfold translatedCone
    rw [twoRayCone_swap (direction (π - β)) (-direction α)]
  have right_swap : translatedCone (base • direction 0 + t • direction (π - β)) (direction (-β)) (direction α) =
      translatedCone (base • direction 0 + t • direction (π - β)) (direction α) (-direction (π - β)) := by
    rw [negative_right]
    unfold translatedCone
    rw [twoRayCone_swap (direction (-β)) (direction α)]
  rw [left_swap] at left_contained
  rw [right_swap] at right_contained
  exact (Set.disjoint_image_iff motion.injective).mp (cones.mono left_contained right_contained)

/-- For a source of curvature at least pi, the Case A angle-containment premises are automatic. -/
theorem opposite_petals_caseA_of_high_source (i : Fin 2) (high : π ≤ graph.curvature source)
    (narrow : net.widenedLeft i + net.widenedRight i < π) :
    Disjoint (net.placedTriangle (true, i.castSucc.castSucc)) (net.placedTriangle (true, i.succ.succ)) := by
  obtain ⟨left_fits, right_fits⟩ := net.opposite_apex_bounds_of_high_source i high
  exact net.opposite_petals_caseA i narrow left_fits.le right_fits.le

/-- The usual maximum-curvature source rule also covers the low-curvature Case A branch. -/
theorem opposite_petals_caseA_of_source_rule (i : Fin 2)
    (source_rule : π ≤ graph.curvature source ∨ ∀ v, graph.curvature v ≤ π)
    (narrow : net.widenedLeft i + net.widenedRight i < π) :
    Disjoint (net.placedTriangle (true, i.castSucc.castSucc)) (net.placedTriangle (true, i.succ.succ)) := by
  rcases source_rule with high | low
  · exact net.opposite_petals_caseA_of_high_source i high narrow
  · obtain ⟨left_fits, right_fits⟩ := net.opposite_apex_bounds_of_all_low i low
    exact net.opposite_petals_caseA i narrow left_fits.le right_fits.le

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
