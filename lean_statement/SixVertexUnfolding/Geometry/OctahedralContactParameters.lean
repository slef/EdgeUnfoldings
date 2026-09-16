import SixVertexUnfolding.Geometry.OctahedralContactVisibility
import SixVertexUnfolding.Geometry.OctahedralSecondContactVisibility

/-! Whole closed remote contact supplies a strictly positive copied-edge parameter at most one. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open Real OctahedralTriangles

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

theorem first_remote_contact_parameter
    (alternative : π ≤ graph.curvature source ∨ graph.curvature (opposite source) ≤ π)
    (x : Plane) (petal : x ∈ net.placedTriangle (true, 1))
    (contact : x ∈ segment ℝ 0 (net.patch 3).right) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      (net.patch 0).right + t • ((net.patch 1).apex - (net.patch 0).right) ∈ segment ℝ 0 (net.patch 3).right := by
  obtain ⟨y, _, on_slit, on_cut⟩ := net.first_remote_contact_reaches_cut alternative x petal contact
  have left_clear : (net.patch 1).left ∉ segment ℝ 0 (net.patch 3).right := by
    intro hit
    have in_last := (net.placedTriangle_convex (false, 3)).segment_subset
      (net.fan_pole_mem 3) (net.patch_right_mem false 3) hit
    exact net.patch_left_ne_zero 1 (net.opposite_fan_pair_meet_only_at_zero 1 (net.patch 1).left
      (net.patch_left_mem false 1) in_last)
  obtain ⟨s, t, hs, ht, sum, position⟩ := on_cut
  have positive : 0 < t := by
    apply lt_of_le_of_ne ht
    intro zero
    have vanish : t = 0 := zero.symm
    have one : s = 1 := by linarith
    have same : (net.patch 1).left = y := by simpa only [vanish, one, one_smul, zero_smul, add_zero] using position
    exact left_clear (same ▸ on_slit)
  have shared := net.consecutive_patch_corner 0
  change (net.patch 0).right = (net.patch 1).left at shared
  refine ⟨t, positive, by linarith, ?_⟩
  have parameter : (net.patch 0).right + t • ((net.patch 1).apex - (net.patch 0).right) = y := by
    rw [shared, ← position, show s = 1 - t by linarith]
    module
  rwa [parameter]

theorem second_remote_contact_parameter
    (alternative : π ≤ graph.curvature source ∨ graph.curvature (opposite source) ≤ π)
    (x : Plane) (petal : x ∈ net.placedTriangle (true, 2))
    (contact : x ∈ segment ℝ 0 (net.patch 0).left) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      (net.patch 2).right + t • ((net.patch 2).apex - (net.patch 2).right) ∈ segment ℝ 0 (net.patch 0).left := by
  obtain ⟨y, _, on_slit, on_cut⟩ := net.second_remote_contact_reaches_cut alternative x petal contact
  have right_clear : (net.patch 2).right ∉ segment ℝ 0 (net.patch 0).left := by
    intro hit
    have in_first := (net.placedTriangle_convex (false, 0)).segment_subset
      (net.fan_pole_mem 0) (net.patch_left_mem false 0) hit
    exact net.patch_right_ne_zero 2 (net.opposite_fan_pair_meet_only_at_zero 2 (net.patch 2).right
      (net.patch_right_mem false 2) in_first)
  obtain ⟨s, t, hs, ht, sum, position⟩ := on_cut
  have positive : 0 < t := by
    apply lt_of_le_of_ne ht
    intro zero
    have vanish : t = 0 := zero.symm
    have one : s = 1 := by linarith
    have same : (net.patch 2).right = y := by simpa only [vanish, one, one_smul, zero_smul, add_zero] using position
    exact right_clear (same ▸ on_slit)
  refine ⟨t, positive, by linarith, ?_⟩
  have parameter : (net.patch 2).right + t • ((net.patch 2).apex - (net.patch 2).right) = y := by
    rw [← position, show s = 1 - t by linarith]
    module
  rwa [parameter]

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
