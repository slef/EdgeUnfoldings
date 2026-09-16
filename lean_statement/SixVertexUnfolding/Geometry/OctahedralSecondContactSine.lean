import SixVertexUnfolding.Geometry.OctahedralSecondContactVisibility
import SixVertexUnfolding.Geometry.ContactSineGeometryRight

/-! The actual second finite contact satisfies the mirrored contact-angle inequality. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open Real EuclideanGeometry OctahedralTriangles

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

theorem second_cut_parameter_mem_petal (t : ℝ) (lower : 0 ≤ t) (upper : t ≤ 1) :
    (net.patch 2).right + t • ((net.patch 2).apex - (net.patch 2).right) ∈ net.placedTriangle (true, 2) := by
  apply (net.placedTriangle_convex (true, 2)).segment_subset (net.patch_right_mem true 2) (net.petal_apex_mem 2)
  refine ⟨1 - t, t, by linarith, lower, by ring, ?_⟩
  module

theorem second_cut_contact_angle_bound
    (alternative : π ≤ graph.curvature source ∨ graph.curvature (opposite source) ≤ π)
    (threshold : π ≤ 2 * graph.curvature (fanNeighbor source slit) + graph.curvature (opposite source))
    (t : ℝ) (positive : 0 < t) (upper : t ≤ 1)
    (contact : (net.patch 2).right + t • ((net.patch 2).apex - (net.patch 2).right) ∈
      segment ℝ 0 (net.patch 0).left) :
    2 * (net.patch 3).leftCorner +
      2 * (2 * π - graph.openingAngle (opposite source) slit 3) +
      graph.curvature (fanNeighbor source (slit + 3)) ≤ π := by
  let ω := graph.openingAngle (opposite source) slit 3
  let δ := 2 * π - ω
  let θ := (net.patch 3).leftCorner
  let gap := graph.curvature (fanNeighbor source (slit + 3))
  let r := dist 0 (net.patch 2).right
  let s := dist (net.patch 3).apex (net.patch 2).right
  have petal := net.second_cut_parameter_mem_petal t positive.le upper
  have reflex := net.second_remote_contact_forces_reflex alternative _ petal contact
  have across := net.second_remote_contact_across_gap alternative _ petal contact
  have δ_pos : 0 < δ := by
    have below := (graph.openingAngle_le_total (opposite source) slit 3).trans_lt (graph.totalAngleAt_lt_two_pi small_faces _)
    dsimp [δ, ω]
    linarith
  have δ_small : δ < π := by dsimp [δ, ω]; linarith
  have gap_pos : 0 < gap := graph.curvature_pos small_faces _
  have corner_sum := net.junction_corner_sum 2
  change (net.patch 2).rightCorner + θ = graph.totalAngleAt (fanNeighbor source ((slit + 2) + 1)) at corner_sum
  rw [add_assoc, show (2 : Fin 4) + 1 = 3 by decide] at corner_sum
  have corner_gap : θ + gap < π := by dsimp [gap]; unfold curvature; linarith
  have r_pos : 0 < r := dist_pos.mpr (net.patch_right_ne_zero 2).symm
  have shared := net.consecutive_patch_corner 2
  change (net.patch 2).right = (net.patch 3).left at shared
  have s_pos : 0 < s := by
    dsimp [s]
    rw [shared]
    exact dist_pos.mpr (ne₁₃_of_not_collinear (net.patch 3).petal_noncollinear).symm
  have at_a : (net.patch 2).right = r • direction ω := by
    dsimp [r, ω]
    rw [net.patch_right, graph.openingPoint_radius]
    rfl
  have at_m : (net.patch 3).apex - (net.patch 2).right = s • direction (ω + π - θ) := by
    have next := net.patch_apex_direction_left 3
    rwa [← shared] at next
  have at_p : (net.patch 2).apex - (net.patch 2).right = s • direction (ω + π - θ - gap) := by
    have previous := net.patch_apex_direction_right 2
    have radii := net.neighboring_apex_radii_equal 2
    change s = dist (net.patch 2).apex (net.patch 2).right at radii
    rw [← radii] at previous
    change _ = s • direction (ω - π + (net.patch 2).rightCorner) at previous
    have equal : ω - π + (net.patch 2).rightCorner = ω + π - θ - gap := by
      dsimp [gap]
      unfold curvature
      linarith
    rwa [equal] at previous
  have contained : (net.patch 3).apex ∈ convexHull ℝ
      ({(net.patch 2).right, 0, (net.patch 2).right + t • ((net.patch 2).apex - (net.patch 2).right)} : Set Plane) := by
    rw [← net.patch_pole 2]
    apply net.right_reflex_contact_containment 2 reflex t positive
    apply (net.local_flank_cuts alternative threshold).2.mono_right
    rw [net.patch_pole]
    exact (convex_segment 0 (net.patch 0).left).segment_subset (left_mem_segment ℝ _ _) contact
  have on_slit := contact
  rw [net.first_slit_position] at on_slit
  obtain ⟨on_cut, inside⟩ := Contact.polar_contact_sine_data_clockwise _ _ _ r s net.slitRadius ω 0 δ θ gap t
    r_pos.le (sin_pos_of_pos_of_lt_pi δ_pos δ_small).le (by dsimp [δ]; ring) at_a at_m at_p on_slit contained
  have positive_sine : 0 < sin (θ + gap + δ) := by
    have left_pos := mul_pos r_pos (sin_pos_of_pos_of_lt_pi δ_pos δ_small)
    rw [on_cut] at left_pos
    exact (mul_pos_iff_of_pos_left (mul_pos positive s_pos)).mp left_pos
  have angle_small : θ + gap + δ < π := by
    by_contra large
    have sine_nonpositive := sin_nonneg_of_nonneg_of_le_pi
      (show 0 ≤ θ + gap + δ - π by linarith [le_of_not_gt large])
      (show θ + gap + δ - π ≤ π by linarith)
    rw [sin_sub_pi] at sine_nonpositive
    linarith
  exact Contact.finite_contact_angle_bound s_pos upper gap_pos
    (show 0 < θ + δ from add_pos (net.patch 3).leftCorner_pos δ_pos) angle_small on_cut inside

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
