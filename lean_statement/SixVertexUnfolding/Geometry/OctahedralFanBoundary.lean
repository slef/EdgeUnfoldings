import SixVertexUnfolding.Geometry.OctahedralPlacedTopology
import SixVertexUnfolding.Geometry.StrictPlanarSectors

/-! Closed fan contacts, exterior witnesses, and the three boundary edges used by the remote-pair argument. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Real OctahedralTriangles OctahedralNet

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
variable (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include small_faces in
theorem openingTriangles_meet_only_at_zero (pole : Fin 6) (slit : Fin 4) (i j : Fin 4)
    (intervening : i.val + 1 < j.val) (x : Plane)
    (left : x ∈ graph.openingTriangle pole slit i) (right : x ∈ graph.openingTriangle pole slit j) : x = 0 := by
  have mono := (graph.openingAngle_strictMono pole slit).monotone
  apply radial_triangles_meet_only_at_zero (graph.opening_radius_pos pole slit i.castSucc)
    (graph.opening_radius_pos pole slit i.succ) (graph.opening_radius_pos pole slit j.castSucc)
    (graph.opening_radius_pos pole slit j.succ)
    (mono (by change i.val ≤ i.val + 1; omega))
    (graph.openingAngle_strictMono pole slit (show i.succ < j.castSucc from intervening))
    (mono (by change j.val ≤ j.val + 1; omega))
    (by rw [graph.openingAngle_step]; exact graph.fanAngle_lt_pi _ _)
    (by rw [graph.openingAngle_step]; exact graph.fanAngle_lt_pi _ _) _ x left right
  have lower := graph.openingAngle_nonneg pole slit i.castSucc
  have upper := graph.openingAngle_le_total pole slit j.succ
  have total := graph.totalAngleAt_lt_two_pi small_faces pole
  linarith

namespace Development

variable {graph small_faces} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

theorem fan_placedTriangle (i : Fin 4) : net.placedTriangle (false, i) = graph.openingTriangle (opposite source) slit i :=
  net.fan.placed_triangle i

theorem opposite_fan_pair_meet_only_at_zero (i : Fin 4) (x : Plane)
    (left : x ∈ net.placedTriangle (false, i)) (right : x ∈ net.placedTriangle (false, i + 2)) : x = 0 := by
  rw [net.fan_placedTriangle] at left right
  fin_cases i
  · exact graph.openingTriangles_meet_only_at_zero small_faces _ _ 0 2 (by decide) x left right
  · exact graph.openingTriangles_meet_only_at_zero small_faces _ _ 1 3 (by decide) x left right
  · exact graph.openingTriangles_meet_only_at_zero small_faces _ _ 0 2 (by decide) x right left
  · exact graph.openingTriangles_meet_only_at_zero small_faces _ _ 1 3 (by decide) x right left

/-- Each remote petal has an explicit equator corner outside its target fan triangle. -/
theorem petal_not_subset_opposite_fan (i : Fin 4) :
    ¬ net.placedTriangle (true, i) ⊆ net.placedTriangle (false, i + 2) := by
  intro inclusion
  have zero := net.opposite_fan_pair_meet_only_at_zero i (net.patch i).left
    (net.patch_left_mem false i) (inclusion (net.patch_left_mem true i))
  rw [net.patch_left] at zero
  have positive : 0 < dist 0 (graph.openingPoint (opposite source) slit i.castSucc) := by
    rw [graph.openingPoint_radius]
    exact graph.opening_radius_pos _ _ _
  rw [zero, dist_self] at positive
  linarith

/-- A fan triangle's boundary consists of its two radial sides and its attached petal's base. -/
theorem fan_frontier_covered (i : Fin 4) : frontier (net.placedTriangle (false, i)) ⊆
    segment ℝ 0 (graph.openingPoint (opposite source) slit i.castSucc) ∪
      (segment ℝ 0 (graph.openingPoint (opposite source) slit i.succ) ∪ net.placedTriangle (true, i)) := by
  intro x boundary
  rw [net.placedTriangle_hull] at boundary
  change x ∈ frontier (convexHull ℝ ({(net.patch i).left, (net.patch i).right, (net.patch i).pole} : Set Plane)) at boundary
  rcases triangle_frontier_subset_edges _ _ _ (net.patch i).fan_noncollinear boundary with base | left | right
  · exact Or.inr (Or.inr ((net.placedTriangle_convex (true, i)).segment_subset
      (net.patch_left_mem true i) (net.patch_right_mem true i) base))
  · left
    rwa [net.patch_pole, net.patch_left, segment_symm] at left
  · exact Or.inr (Or.inl (by rwa [net.patch_pole, net.patch_right, segment_symm] at right))

theorem radial_edge_in_previous_fan (i : Fin 3) :
    segment ℝ 0 (graph.openingPoint (opposite source) slit i.succ.castSucc) ⊆ net.placedTriangle (false, i.castSucc) := by
  apply (net.placedTriangle_convex _).segment_subset (net.fan_pole_mem _)
  have member := net.patch_right_mem false i.castSucc
  rwa [net.patch_right] at member

theorem radial_edge_in_next_fan (i : Fin 3) :
    segment ℝ 0 (graph.openingPoint (opposite source) slit i.castSucc.succ) ⊆ net.placedTriangle (false, i.succ) := by
  apply (net.placedTriangle_convex _).segment_subset (net.fan_pole_mem _)
  have member := net.patch_left_mem false i.succ
  rwa [net.patch_left] at member

end Development
end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
