import SixVertexUnfolding.Geometry.MetricKitePolarFrame
import SixVertexUnfolding.Geometry.JunctionDevelopedKites
import SixVertexUnfolding.Geometry.IncidentWedgeTransitions

/-! Start the expanding-region induction with the whole first kite.
Its far endpoint need not have a flat chart and may be an original vertex. -/

namespace SixVertexUnfolding.ConvexPolyhedron.IncidentTriangles

open Real Set EuclideanGeometry Wedge

variable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a}
    {u v : T.vertices} {edge : T.graph.Adj u v}
    {chart : P.CutVoronoiChart a (T.vertexTarget u)} {φ : ℝ}
    (D : IncidentTriangles T edge chart φ)

/-- The first actual kite is enclosed with exactly its source-angle charge. -/
theorem initial_kite_in_wedge :
    D.developedKite ⊆ D.incomingWedge (π / 2 + D.model.sourceAngle) := by
  let M := D.model
  let L := dist M.right M.left
  let d := dist M.right M.first
  let θ := angle M.left M.right M.first
  have lp : 0 < L := dist_pos.mpr M.base_different.symm
  have dp : 0 < d := dist_pos.mpr (ne₁₃_of_not_collinear (show
      ¬ Collinear ℝ ({M.right, M.left, M.first} : Set Plane) by
        simpa only [insert_comm] using M.base_first_noncollinear))
  have tp : 0 < θ := angle_pos_of_not_collinear M.base_first_noncollinear
  have ts : θ < π := angle_lt_pi_of_not_collinear M.base_first_noncollinear
  obtain ⟨frame, at_right, at_left, at_first, at_second⟩ := M.exists_reverse_polar_frame
  have apex : angle 0 (d • direction θ) (L • direction 0) = M.sourceAngle := by
    have preserved := frame.toAffineIsometry.angle_map M.right M.first M.left
    change angle (frame M.right) (frame M.first) (frame M.left) = _ at preserved
    rw [at_right, at_left, at_first, angle_comm M.right M.first M.left] at preserved
    exact preserved
  have step := gap_rotate_and_move_with_sources (0 : Plane) (α := θ) (β := -θ + 2 * π)
    (γ := -θ) (δ := θ) (ω := π / 2) dp lp (by linarith) (by linarith)
    (Or.inr ⟨le_rfl, le_rfl⟩) le_rfl (by
      simp only [neg_add_cancel, zero_div, zero_add] at ⊢
      rw [apex]
      linarith [M.sourceAngle_lt_pi])
  dsimp only at step
  simp only [neg_add_cancel, zero_div, zero_add, add_zero, apex] at step
  obtain ⟨radius, Θ, rp, Thp, Ths, source_position, _, _, _, returned⟩ := step
  have radius_eq : radius = P.surfaceDist a (T.vertexTarget u) := by
    have length := frame.dist_map M.first M.left
    rw [at_first, at_left, source_position, dist_eq_norm, add_sub_cancel_left,
      norm_smul, direction_norm, mul_one, Real.norm_eq_abs, abs_of_pos rp] at length
    exact length.trans M.left_radius
  have corner_eq : π - Θ = angle M.first M.left M.right := by
    have corner := next_root_corner (0 : Plane) (L := L) (D := radius) (Θ := Θ) (m := 0) lp rp Thp Ths
    simp only [zero_add, add_zero] at corner
    rw [← source_position] at corner
    have preserved := frame.toAffineIsometry.angle_map M.first M.left M.right
    change angle (frame M.first) (frame M.left) (frame M.right) = _ at preserved
    rw [at_first, at_left, at_right] at preserved
    exact corner.symm.trans preserved
  let back := frame.symm.trans D.motion
  have back_apply (x : Plane) : back x = D.motion (frame.symm x) := rfl
  have root : back (L • direction 0) = chart.origin := by
    rw [back_apply, ← at_left, frame.symm_apply_apply, D.at_junction]
  have base_length : L = dist (u : Space) (v : Space) :=
    (dist_comm M.right M.left).trans M.base_length
  have on_axis : back (L • direction 0 + L • direction π) = chart.origin + L • direction φ := by
    have cancel : L • direction 0 + L • direction π = (0 : Plane) := by
      simpa only [zero_add, add_zero] using next_root_back_ray (0 : Plane) L 0
    rw [cancel, back_apply, ← at_right, frame.symm_apply_apply, D.at_neighbor, ← base_length]
  have image := centered_wedge_image back (L • direction 0) chart.origin lp root on_axis
    radius (π / 2 + M.sourceAngle) (π - Θ)
  rw [show π - (π - Θ) = Θ by ring, show π + (π - Θ) = 2 * π - Θ by ring] at image
  have target : back '' {x | x - L • direction 0 ∈
      polarRegion radius (π / 2 + M.sourceAngle) Θ (2 * π - Θ)} =
        D.incomingWedge (π / 2 + M.sourceAngle) := by
    simpa only [radius_eq, corner_eq, incomingWedge] using image
  have triangle_image (p l r : Plane) : back '' convexHull ℝ ({p, l, r} : Set Plane) =
      convexHull ℝ ({back p, back l, back r} : Set Plane) := by
    change back.toAffineMap '' _ = _
    rw [back.toAffineMap.image_convexHull]
    simp only [image_insert_eq, image_singleton]
    rfl
  have kite_image : back '' gapKite 0 d L (-θ) θ = D.developedKite := by
    rw [gapKite, image_union, triangle_image, triangle_image]
    simp only [neg_add_cancel, zero_div, zero_add]
    simp only [back_apply]
    rw [← at_right, ← at_left, ← at_first, ← at_second]
    simp only [frame.symm_apply_apply]
    unfold developedKite
    apply congrArg₂ (fun A B : Set Plane => A ∪ B)
    · apply congrArg (convexHull ℝ)
      ext x
      simp only [mem_insert_iff, mem_singleton_iff]
      tauto
    · apply congrArg (convexHull ℝ)
      ext x
      simp only [mem_insert_iff, mem_singleton_iff]
      tauto
  rw [← kite_image, ← target]
  apply image_mono
  rw [returned]
  exact subset_union_right

end SixVertexUnfolding.ConvexPolyhedron.IncidentTriangles
