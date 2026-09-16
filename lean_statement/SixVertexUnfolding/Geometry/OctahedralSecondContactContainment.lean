import SixVertexUnfolding.Geometry.FourTriangleLastCone
import SixVertexUnfolding.Geometry.OctahedralContactContainment
import SixVertexUnfolding.Geometry.OctahedralSecondContactEntry

/-! Finite contact containment and the curvature obstruction at the other end of a junction. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open Real EuclideanGeometry OctahedralTriangles

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

theorem next_apex_in_reflex_contact_cone (i : Fin 3) (reflex : π < (net.patch i.castSucc).rightCorner) :
    (net.patch i.succ).apex - (net.patch i.castSucc).right ∈
      twoRayCone ((net.patch i.castSucc).pole - (net.patch i.castSucc).right)
        ((net.patch i.castSucc).apex - (net.patch i.castSucc).right) := by
  apply (net.junctionChain i).last_ray_in_complementary_cone
  · rw [net.junction_angle_sum]
    exact graph.totalAngleAt_lt_two_pi small_faces _
  · change π < angle (net.patch i.castSucc).apex (net.patch i.castSucc).right (net.patch i.castSucc).left +
      angle (net.patch i.castSucc).left (net.patch i.castSucc).right (net.patch i.castSucc).pole
    unfold DevelopedPatch.rightCorner at reflex
    have first := angle_comm (net.patch i.castSucc).apex (net.patch i.castSucc).right (net.patch i.castSucc).left
    have second := angle_comm (net.patch i.castSucc).left (net.patch i.castSucc).right (net.patch i.castSucc).pole
    linarith

theorem right_reflex_contact_containment (i : Fin 3) (reflex : π < (net.patch i.castSucc).rightCorner)
    (t : ℝ) (positive : 0 < t)
    (clear : Disjoint (net.placedTriangle (true, i.succ))
      (segment ℝ (net.patch i.castSucc).pole
        ((net.patch i.castSucc).right + t • ((net.patch i.castSucc).apex - (net.patch i.castSucc).right)))) :
    (net.patch i.succ).apex ∈ convexHull ℝ
      ({(net.patch i.castSucc).right, (net.patch i.castSucc).pole,
        (net.patch i.castSucc).right + t • ((net.patch i.castSucc).apex - (net.patch i.castSucc).right)} : Set Plane) := by
  apply triangle_contains_of_cone_and_segment_clear
  · have cone := mem_twoRayCone_scaled_generators _ _ _ 1 t (by norm_num) positive
      (net.next_apex_in_reflex_contact_cone i reflex)
    simpa only [one_smul, add_sub_cancel_left] using cone
  · apply clear.mono_left
    rw [net.consecutive_patch_corner]
    exact (net.placedTriangle_convex (true, i.succ)).segment_subset
      (net.patch_left_mem true i.succ) (net.petal_apex_mem i.succ)

/-- The mirrored projection inequality uses the next petal's left edge and its actual spatial lengths. -/
theorem source_curvature_lt_pi_of_right_junction_containment (i : Fin 3) (t : ℝ)
    (lower : 0 ≤ t) (upper : t ≤ 1)
    (contained : (net.patch i.succ).apex ∈ convexHull ℝ
      ({(net.patch i.castSucc).right, (net.patch i.castSucc).pole,
        (net.patch i.castSucc).right + t • ((net.patch i.castSucc).apex - (net.patch i.castSucc).right)} : Set Plane)) :
    graph.curvature source < π := by
  have pole_same : (net.patch i.castSucc).pole = (net.patch i.succ).pole := by rw [net.patch_pole, net.patch_pole]
  have apex_ne : (net.patch i.succ).apex ≠ (net.patch i.castSucc).right := by
    rw [net.consecutive_patch_corner]
    exact (ne₁₃_of_not_collinear (net.patch i.succ).petal_noncollinear).symm
  have not_pole : (net.patch i.succ).apex ≠ (net.patch i.castSucc).pole := by
    rw [pole_same]
    exact net.petal_apex_ne_pole i.succ
  have metric := Contact.contact_metric_obtuse_at (net.patch i.castSucc).right (net.patch i.castSucc).pole
    (net.patch i.succ).apex (net.patch i.castSucc).apex apex_ne
    (net.neighboring_apex_radii_equal i).symm (net.neighboring_apex_copies_distinct i).symm t lower upper contained not_pole
  rw [net.consecutive_patch_corner, pole_same, (net.patch i.succ).petal_left, (net.patch i.succ).fan_left] at metric
  apply graph.source_curvature_lt_pi_of_obtuse small_faces source (slit + i.succ)
  have comparison := (sq_le_sq₀ (dist_nonneg : 0 ≤ dist (graph.vertex (opposite source) : Space) (graph.vertex source))
    (dist_nonneg : 0 ≤ dist (net.patch i.succ).pole (net.patch i.succ).apex)).mpr (net.patch i.succ).pole_distance_ge
  linarith

theorem source_curvature_lt_pi_of_second_cut_contact
    (alternative : π ≤ graph.curvature source ∨ graph.curvature (opposite source) ≤ π)
    (threshold : π ≤ 2 * graph.curvature (fanNeighbor source slit) + graph.curvature (opposite source))
    (reflex : π < (net.patch 2).rightCorner) (t : ℝ) (positive : 0 < t) (upper : t ≤ 1)
    (contact : (net.patch 2).right + t • ((net.patch 2).apex - (net.patch 2).right) ∈
      segment ℝ 0 (net.patch 0).left) : graph.curvature source < π := by
  apply net.source_curvature_lt_pi_of_right_junction_containment 2 t positive.le upper
  apply net.right_reflex_contact_containment 2 reflex t positive
  apply (net.local_flank_cuts alternative threshold).2.mono_right
  change segment ℝ (net.patch 2).pole _ ⊆ segment ℝ 0 (net.patch 0).left
  rw [net.patch_pole]
  exact (convex_segment 0 (net.patch 0).left).segment_subset (left_mem_segment ℝ _ _) contact

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
