import SixVertexUnfolding.Geometry.ConeTriangleContainment
import SixVertexUnfolding.Geometry.FourTriangleCone
import SixVertexUnfolding.Geometry.OctahedralLocalBoundary
import SixVertexUnfolding.Geometry.OctahedralContactProjection
import SixVertexUnfolding.Geometry.OctahedralContactEntry

/-! Reflex cut contact traps the neighboring source copy in the finite contact triangle. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open Real EuclideanGeometry OctahedralTriangles

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

/-- The actual junction angle sum places the previous apex in the cone complementary to a reflex next patch. -/
theorem previous_apex_in_reflex_contact_cone (i : Fin 3) (reflex : π < (net.patch i.succ).leftCorner) :
    (net.patch i.castSucc).apex - (net.patch i.castSucc).right ∈
      twoRayCone ((net.patch i.castSucc).pole - (net.patch i.castSucc).right)
        ((net.patch i.succ).apex - (net.patch i.castSucc).right) := by
  apply (net.junctionChain i).first_ray_in_complementary_cone
  · rw [net.junction_angle_sum]
    exact graph.totalAngleAt_lt_two_pi small_faces _
  · change π < angle (net.patch i.castSucc).pole (net.patch i.castSucc).right (net.patch i.succ).right +
      angle (net.patch i.succ).right (net.patch i.castSucc).right (net.patch i.succ).apex
    rw [net.consecutive_patch_corner, net.patch_pole, ← net.patch_pole i.succ]
    exact reflex

/-- The neighboring copied edge cannot cross the finite contact base, so its apex stays in the contact triangle. -/
theorem reflex_contact_containment (i : Fin 3) (reflex : π < (net.patch i.succ).leftCorner)
    (t : ℝ) (positive : 0 < t)
    (clear : Disjoint (net.placedTriangle (true, i.castSucc))
      (segment ℝ (net.patch i.castSucc).pole
        ((net.patch i.castSucc).right + t • ((net.patch i.succ).apex - (net.patch i.castSucc).right)))) :
    (net.patch i.castSucc).apex ∈ convexHull ℝ
      ({(net.patch i.castSucc).right, (net.patch i.castSucc).pole,
        (net.patch i.castSucc).right + t • ((net.patch i.succ).apex - (net.patch i.castSucc).right)} : Set Plane) := by
  apply triangle_contains_of_cone_and_segment_clear
  · have cone := mem_twoRayCone_scaled_generators _ _ _ 1 t (by norm_num) positive
      (net.previous_apex_in_reflex_contact_cone i reflex)
    simpa only [one_smul, add_sub_cancel_left] using cone
  · apply clear.mono_left
    exact (net.placedTriangle_convex (true, i.castSucc)).segment_subset
      (net.patch_right_mem true i.castSucc) (net.petal_apex_mem i.castSucc)

/-- With the closed contact parameter at most one, containment gives the strict source-curvature obstruction. -/
theorem source_curvature_lt_pi_of_reflex_contact (i : Fin 3) (reflex : π < (net.patch i.succ).leftCorner)
    (t : ℝ) (positive : 0 < t) (upper : t ≤ 1)
    (clear : Disjoint (net.placedTriangle (true, i.castSucc))
      (segment ℝ (net.patch i.castSucc).pole
        ((net.patch i.castSucc).right + t • ((net.patch i.succ).apex - (net.patch i.castSucc).right)))) :
    graph.curvature source < π :=
  net.source_curvature_lt_pi_of_junction_containment i t positive.le upper
    (net.reflex_contact_containment i reflex t positive clear)

/-- For the first remote contact, the completed local boundary theorem supplies the finite-base avoidance. -/
theorem source_curvature_lt_pi_of_first_cut_contact
    (alternative : π ≤ graph.curvature source ∨ graph.curvature (opposite source) ≤ π)
    (threshold : π ≤ 2 * graph.curvature (fanNeighbor source slit) + graph.curvature (opposite source))
    (reflex : π < (net.patch 1).leftCorner) (t : ℝ) (positive : 0 < t) (upper : t ≤ 1)
    (contact : (net.patch 0).right + t • ((net.patch 1).apex - (net.patch 0).right) ∈
      segment ℝ 0 (net.patch 3).right) : graph.curvature source < π := by
  apply net.source_curvature_lt_pi_of_reflex_contact 0 reflex t positive upper
  apply (net.local_flank_cuts alternative threshold).1.mono_right
  change segment ℝ (net.patch 0).pole _ ⊆ segment ℝ 0 (net.patch 3).right
  rw [net.patch_pole]
  exact (convex_segment 0 (net.patch 3).right).segment_subset (left_mem_segment ℝ _ _) contact

/-- For a point on the copied cut edge, actual contact itself supplies the reflex-corner premise. -/
theorem source_curvature_lt_pi_of_first_cut_edge_contact
    (alternative : π ≤ graph.curvature source ∨ graph.curvature (opposite source) ≤ π)
    (threshold : π ≤ 2 * graph.curvature (fanNeighbor source slit) + graph.curvature (opposite source))
    (t : ℝ) (positive : 0 < t) (upper : t ≤ 1)
    (contact : (net.patch 0).right + t • ((net.patch 1).apex - (net.patch 0).right) ∈
      segment ℝ 0 (net.patch 3).right) : graph.curvature source < π := by
  have in_petal : (net.patch 0).right + t • ((net.patch 1).apex - (net.patch 0).right) ∈
      net.placedTriangle (true, 1) := by
    apply (net.placedTriangle_convex (true, 1)).segment_subset
      (net.patch_left_mem true 1) (net.petal_apex_mem 1)
    have shared := net.consecutive_patch_corner 0
    change (net.patch 0).right = (net.patch 1).left at shared
    rw [shared]
    refine ⟨1 - t, t, by linarith, positive.le, by ring, ?_⟩
    module
  have reflex := net.first_remote_contact_forces_reflex alternative _ in_petal contact
  exact net.source_curvature_lt_pi_of_first_cut_contact alternative threshold reflex t positive upper contact

/-- At a high-curvature source, no point of this remote copied cut edge can reach the opposite finite slit. -/
theorem first_cut_edge_cannot_reach_last_slit (source_high : π ≤ graph.curvature source)
    (threshold : π ≤ 2 * graph.curvature (fanNeighbor source slit) + graph.curvature (opposite source))
    (t : ℝ) (positive : 0 < t) (upper : t ≤ 1) :
    (net.patch 0).right + t • ((net.patch 1).apex - (net.patch 0).right) ∉ segment ℝ 0 (net.patch 3).right := by
  intro contact
  have impossible := net.source_curvature_lt_pi_of_first_cut_edge_contact (Or.inl source_high) threshold t positive upper contact
  linarith

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
