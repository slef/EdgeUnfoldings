import SixVertexUnfolding.Geometry.TriangleFrame
import SixVertexUnfolding.Geometry.RadialTriangleCorners
import Mathlib.Topology.Order.ProjIcc

/-! A sufficiently small circular section of a nondegenerate triangle is
parametrized by an interval of exactly its corner angle. -/

namespace SixVertexUnfolding

open Set Real EuclideanGeometry

/-- Every sufficiently short ray within a triangle's corner lies in the triangle. -/
theorem radial_triangle_small_arcs (r s α : ℝ) (rp : 0 < r) (sp : 0 < s)
    (ap : 0 < α) (short : α < π) :
    ∃ ε > 0, ∀ ρ ∈ Ioo (0 : ℝ) ε, ∀ θ ∈ Icc (0 : ℝ) α,
      ρ • direction θ ∈ convexHull ℝ ({0, r • direction 0, s • direction α} : Set Plane) := by
  let b := r • direction 0
  let c := s • direction α
  let base (x : Plane) := det (c - b) (x - b)
  have area : 0 < det b c := by
    change 0 < det (r • direction 0) (s • direction α)
    rw [det_smul_left, det_smul_right, direction_det, sub_zero]
    exact mul_pos rp (mul_pos sp (sin_pos_of_pos_of_lt_pi ap short))
  have base_zero : base 0 = det b c := by
    simp only [base, det, PiLp.sub_apply, PiLp.zero_apply]
    ring
  have continuous : Continuous base := (detHeight _).continuous.comp (continuous_id.sub continuous_const)
  obtain ⟨ε, ep, inside⟩ := Metric.isOpen_iff.mp (isOpen_lt continuous_const continuous) 0
    (by change 0 < base 0; rwa [base_zero])
  refine ⟨ε, ep, ?_⟩
  intro ρ hr θ hθ
  apply triangle_mem_of_three_halfplanes b c _ area
  · change 0 ≤ det (r • direction 0) (ρ • direction θ)
    rw [det_smul_left, det_smul_right, direction_det, sub_zero]
    exact mul_nonneg rp.le (mul_nonneg hr.1.le (sin_nonneg_of_nonneg_of_le_pi hθ.1 (hθ.2.trans short.le)))
  · change 0 ≤ det (ρ • direction θ) (s • direction α)
    rw [det_smul_left, det_smul_right, direction_det]
    exact mul_nonneg hr.1.le (mul_nonneg sp.le (sin_nonneg_of_nonneg_of_le_pi
      (sub_nonneg.mpr hθ.2) (by linarith [hθ.1])))
  · exact (inside (by rw [Metric.mem_ball, dist_comm, polar_radius _ _ hr.1.le]; exact hr.2)).le

/-- An actual circular section, with its ordinary corner angle as parameter length. -/
structure TriangleCornerArc (p l r : Plane) (ρ : ℝ) where
  point : C(ℝ, convexHull ℝ ({p, l, r} : Set Plane))
  radius : ∀ θ, dist (point θ : Plane) l = ρ
  angle_bound : ∀ s ∈ Icc (0 : ℝ) (angle p l r), ∀ t ∈ Icc (0 : ℝ) (angle p l r),
    angle (point s : Plane) l (point t : Plane) ≤ dist s t
  covers : ∀ x : convexHull ℝ ({p, l, r} : Set Plane), dist (x : Plane) l = ρ →
    ∃ θ ∈ Icc (0 : ℝ) (angle p l r), point θ = x

/-- This arc is constructed by a rigid frame and a clamped ordinary polar parameter. -/
theorem exists_triangle_corner_arcs (p l r : Plane)
    (noncollinear : ¬ Collinear ℝ ({p, l, r} : Set Plane)) :
    ∃ ε > 0, ∀ ρ ∈ Ioo (0 : ℝ) ε, Nonempty (TriangleCornerArc p l r ρ) := by
  have order_triangle : ¬ Collinear ℝ ({l, p, r} : Set Plane) := by
    simpa only [Set.insert_comm] using noncollinear
  obtain ⟨motion, at_l, at_p, at_r⟩ := exists_upper_triangle_frame l p r order_triangle
  have ap : 0 < angle p l r := angle_pos_of_not_collinear noncollinear
  have short : angle p l r < π := angle_lt_pi_of_not_collinear noncollinear
  have lp : 0 < dist l p := dist_pos.mpr (ne₁₂_of_not_collinear order_triangle)
  have lr : 0 < dist l r := dist_pos.mpr (ne₁₃_of_not_collinear order_triangle)
  obtain ⟨ε, ep, arcs⟩ := radial_triangle_small_arcs _ _ _ lp lr ap short
  have image_triangle : motion '' convexHull ℝ ({p, l, r} : Set Plane) =
      convexHull ℝ ({0, dist l p • direction 0, dist l r • direction (angle p l r)} : Set Plane) := by
    change motion.toAffineMap '' _ = _
    rw [motion.toAffineMap.image_convexHull]
    simp only [image_insert_eq, image_singleton]
    change convexHull ℝ ({motion p, motion l, motion r} : Set Plane) = _
    rw [at_l, at_p, at_r]
    rw [Set.insert_comm]
  refine ⟨ε, ep, ?_⟩
  intro ρ hr
  let clamp := projIcc (0 : ℝ) (angle p l r) ap.le
  let q (θ : ℝ) : Plane := motion.symm (ρ • direction (clamp θ))
  have in_triangle (θ : ℝ) : q θ ∈ convexHull ℝ ({p, l, r} : Set Plane) := by
    have member := arcs ρ hr (clamp θ) (clamp θ).property
    rw [← image_triangle] at member
    obtain ⟨x, hx, equal⟩ := member
    simpa only [q, ← equal, motion.symm_apply_apply] using hx
  have point_continuous : Continuous q := motion.symm.continuous.comp
    (continuous_const.smul (direction_continuous.comp
      (continuous_subtype_val.comp continuous_projIcc)))
  let point : C(ℝ, convexHull ℝ ({p, l, r} : Set Plane)) :=
    ⟨fun θ => ⟨q θ, in_triangle θ⟩, point_continuous.subtype_mk _⟩
  have placed (θ : ℝ) : motion (point θ : Plane) = ρ • direction (clamp θ) := motion.apply_symm_apply _
  have unclamped (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) (angle p l r)) : (clamp θ : ℝ) = θ := by
    exact congrArg Subtype.val (projIcc_of_mem ap.le hθ)
  refine ⟨⟨point, ?_, ?_, ?_⟩⟩
  · intro θ
    rw [← motion.dist_map, placed, at_l, dist_comm, polar_radius _ _ hr.1.le]
  · intro s hs t ht
    have measured := motion.toAffineIsometry.angle_map (point s : Plane) l (point t : Plane)
    change angle (motion (point s : Plane)) (motion l) (motion (point t : Plane)) = _ at measured
    rw [placed, placed, at_l, unclamped s hs, unclamped t ht] at measured
    rw [← measured]
    rcases le_total s t with h | h
    · rw [radial_angle _ _ _ _ hr.1 hr.1 (sub_nonneg.mpr h) (by linarith [hs.1, ht.2]),
        Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr h), neg_sub]
    · rw [angle_comm, radial_angle _ _ _ _ hr.1 hr.1 (sub_nonneg.mpr h) (by linarith [ht.1, hs.2]),
        Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr h)]
  · intro x radius
    have mx : motion (x : Plane) ∈ convexHull ℝ
        ({0, dist l p • direction 0, dist l r • direction (angle p l r)} : Set Plane) := by
      rw [← image_triangle]
      exact mem_image_of_mem motion x.property
    have length : dist 0 (motion (x : Plane)) = ρ := by
      rw [← at_l, motion.dist_map, dist_comm]
      exact radius
    have nonzero : motion (x : Plane) ≠ 0 := by
      intro zero
      rw [zero, dist_self] at length
      exact (ne_of_gt hr.1) length.symm
    obtain ⟨θ, lower, upper, expression⟩ := radial_triangle_polar_representation _ _ _ _ lp lr ap
      (by simpa only [sub_zero] using short) _ nonzero mx
    refine ⟨θ, ⟨lower, upper⟩, Subtype.ext ?_⟩
    apply motion.injective
    rw [placed, unclamped θ ⟨lower, upper⟩, expression, length]

end SixVertexUnfolding
