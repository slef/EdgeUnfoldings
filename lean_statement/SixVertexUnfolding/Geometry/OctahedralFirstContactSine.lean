import SixVertexUnfolding.Geometry.OctahedralContactVisibility
import SixVertexUnfolding.Geometry.ContactSineGeometry

/-! The actual first finite contact satisfies the contact-angle inequality. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open Real EuclideanGeometry OctahedralTriangles

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

theorem first_cut_parameter_mem_petal (t : ℝ) (lower : 0 ≤ t) (upper : t ≤ 1) :
    (net.patch 0).right + t • ((net.patch 1).apex - (net.patch 0).right) ∈ net.placedTriangle (true, 1) := by
  have shared := net.consecutive_patch_corner 0
  change (net.patch 0).right = (net.patch 1).left at shared
  rw [shared]
  apply (net.placedTriangle_convex (true, 1)).segment_subset (net.patch_left_mem true 1) (net.petal_apex_mem 1)
  refine ⟨1 - t, t, by linarith, lower, by ring, ?_⟩
  module

/-- All directions and sine hypotheses are derived from the actual closed contact in this net. -/
theorem first_cut_contact_angle_bound
    (alternative : π ≤ graph.curvature source ∨ graph.curvature (opposite source) ≤ π)
    (threshold : π ≤ 2 * graph.curvature (fanNeighbor source slit) + graph.curvature (opposite source))
    (t : ℝ) (positive : 0 < t) (upper : t ≤ 1)
    (contact : (net.patch 0).right + t • ((net.patch 1).apex - (net.patch 0).right) ∈
      segment ℝ 0 (net.patch 3).right) :
    2 * (net.patch 0).rightCorner +
      2 * (graph.openingAngle (opposite source) slit 1 + graph.curvature (opposite source)) +
      graph.curvature (fanNeighbor source (slit + 1)) ≤ π := by
  let ω := graph.openingAngle (opposite source) slit 1
  let Γ := graph.totalAngleAt (opposite source)
  let δ := ω + graph.curvature (opposite source)
  let θ := (net.patch 0).rightCorner
  let gap := graph.curvature (fanNeighbor source (slit + 1))
  let r := dist 0 (net.patch 0).right
  let s := dist (net.patch 0).apex (net.patch 0).right
  have petal := net.first_cut_parameter_mem_petal t positive.le upper
  have reflex := net.first_remote_contact_forces_reflex alternative _ petal contact
  have across := net.first_remote_contact_across_gap alternative _ petal contact
  have δ_pos : 0 < δ := by
    dsimp [δ, ω]
    linarith [graph.openingAngle_nonneg (opposite source) slit 1, graph.curvature_pos small_faces (opposite source)]
  have δ_small : δ < π := by
    dsimp [δ, ω]
    unfold curvature at *
    linarith
  have turn : Γ + δ = ω + 2 * π := by dsimp [Γ, δ, curvature]; ring
  have gap_pos : 0 < gap := graph.curvature_pos small_faces _
  have corner_sum := net.junction_corner_sum 0
  change θ + (net.patch 1).leftCorner = graph.totalAngleAt (fanNeighbor source ((slit + 0) + 1)) at corner_sum
  simp only [add_zero] at corner_sum
  have corner_gap : θ + gap < π := by dsimp [gap]; unfold curvature; linarith
  have r_pos : 0 < r := dist_pos.mpr (net.patch_right_ne_zero 0).symm
  have s_pos : 0 < s := dist_pos.mpr (net.petal_apex_ne_right 0)
  have at_a : (net.patch 0).right = r • direction ω := by
    dsimp [r, ω]
    rw [net.patch_right, graph.openingPoint_radius]
    rfl
  have at_m : (net.patch 0).apex - (net.patch 0).right = s • direction (ω - π + θ) :=
    net.patch_apex_direction_right 0
  have at_p : (net.patch 1).apex - (net.patch 0).right = s • direction (ω - π + θ + gap) := by
    have next := net.patch_apex_direction_left 1
    have shared := net.consecutive_patch_corner 0
    change (net.patch 0).right = (net.patch 1).left at shared
    rw [← shared] at next
    have radii := net.neighboring_apex_radii_equal 0
    change dist (net.patch 1).apex (net.patch 0).right = s at radii
    rw [radii] at next
    change _ = s • direction (ω + π - (net.patch 1).leftCorner) at next
    have equal : ω + π - (net.patch 1).leftCorner = ω - π + θ + gap := by
      dsimp [gap]
      unfold curvature
      linarith
    rwa [equal] at next
  have contained : (net.patch 0).apex ∈ convexHull ℝ
      ({(net.patch 0).right, 0, (net.patch 0).right + t • ((net.patch 1).apex - (net.patch 0).right)} : Set Plane) := by
    rw [← net.patch_pole 0]
    apply net.reflex_contact_containment 0 reflex t positive
    apply (net.local_flank_cuts alternative threshold).1.mono_right
    rw [net.patch_pole]
    exact (convex_segment 0 (net.patch 3).right).segment_subset (left_mem_segment ℝ _ _) contact
  have on_slit := contact
  rw [net.last_slit_position_total] at on_slit
  obtain ⟨on_cut, inside⟩ := Contact.polar_contact_sine_data _ _ _ r s net.slitRadius ω Γ δ θ gap t
    r_pos.le (sin_pos_of_pos_of_lt_pi δ_pos δ_small).le turn at_a at_m at_p on_slit contained
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
    (show 0 < θ + δ from add_pos (net.patch 0).rightCorner_pos δ_pos) angle_small on_cut inside

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
