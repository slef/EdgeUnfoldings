import SixVertexUnfolding.Geometry.TriangleCornerArcs

/-! A uniform small radius fills every direction in a triangle corner.
The origin and the initial angle can be arbitrary. -/

namespace SixVertexUnfolding

open Set Real

/-- A radial triangle contains a uniform small sector, including both bounding rays. -/
theorem radial_triangle_small_sector (r s α β : ℝ) (rp : 0 < r) (sp : 0 < s)
    (ordered : α < β) (short : β - α < π) :
    ∃ ε > 0, ∀ ρ ∈ Ioo (0 : ℝ) ε, ∀ θ ∈ Icc α β,
      ρ • direction θ ∈ convexHull ℝ ({0, r • direction α, s • direction β} : Set Plane) := by
  let b := r • direction α
  let c := s • direction β
  let base (x : Plane) := det (c - b) (x - b)
  have area : 0 < det b c := by
    change 0 < det (r • direction α) (s • direction β)
    rw [det_smul_left, det_smul_right, direction_det]
    exact mul_pos rp (mul_pos sp (sin_pos_of_pos_of_lt_pi (sub_pos.mpr ordered) short))
  have base_zero : base 0 = det b c := by
    simp only [base, det, PiLp.sub_apply, PiLp.zero_apply]
    ring
  have continuous : Continuous base := (detHeight _).continuous.comp (continuous_id.sub continuous_const)
  obtain ⟨ε, ep, inside⟩ := Metric.isOpen_iff.mp (isOpen_lt continuous_const continuous) 0
    (by change 0 < base 0; rwa [base_zero])
  refine ⟨ε, ep, ?_⟩
  intro ρ hr θ hθ
  apply triangle_mem_of_three_halfplanes b c _ area
  · change 0 ≤ det (r • direction α) (ρ • direction θ)
    rw [det_smul_left, det_smul_right, direction_det]
    exact mul_nonneg rp.le (mul_nonneg hr.1.le (sin_nonneg_of_nonneg_of_le_pi
      (sub_nonneg.mpr hθ.1) (by linarith [hθ.2])))
  · change 0 ≤ det (ρ • direction θ) (s • direction β)
    rw [det_smul_left, det_smul_right, direction_det]
    exact mul_nonneg hr.1.le (mul_nonneg sp.le (sin_nonneg_of_nonneg_of_le_pi
      (sub_nonneg.mpr hθ.2) (by linarith [hθ.1])))
  · exact (inside (by rw [Metric.mem_ball, dist_comm, polar_radius _ _ hr.1.le]; exact hr.2)).le

/-- The same sector statement in any translated coordinate frame. -/
theorem translated_triangle_small_sector (o : Plane) (r s α β : ℝ) (rp : 0 < r) (sp : 0 < s)
    (ordered : α < β) (short : β - α < π) :
    ∃ ε > 0, ∀ ρ ∈ Ioo (0 : ℝ) ε, ∀ θ ∈ Icc α β,
      o + ρ • direction θ ∈
        convexHull ℝ ({o, o + r • direction α, o + s • direction β} : Set Plane) := by
  obtain ⟨ε, ep, inside⟩ := radial_triangle_small_sector r s α β rp sp ordered short
  refine ⟨ε, ep, ?_⟩
  intro ρ hr θ hθ
  let shift : Plane →ᵃ[ℝ] Plane := (AffineEquiv.constVAdd ℝ Plane o).toAffineMap
  have image_triangle : shift '' convexHull ℝ ({0, r • direction α, s • direction β} : Set Plane) =
      convexHull ℝ ({o, o + r • direction α, o + s • direction β} : Set Plane) := by
    rw [shift.image_convexHull]
    simp only [image_insert_eq, image_singleton]
    change convexHull ℝ ({o + 0, o + r • direction α, o + s • direction β} : Set Plane) = _
    rw [add_zero]
  rw [← image_triangle]
  exact ⟨_, inside ρ hr θ hθ, rfl⟩

/-- Either ordering of the two boundary rays gives the same filled corner. -/
theorem triangle_small_sector_unordered (o : Plane) (r s α β : ℝ) (rp : 0 < r) (sp : 0 < s)
    (different : α ≠ β) (short : |β - α| < π) :
    ∃ ε > 0, ∀ ρ ∈ Ioo (0 : ℝ) ε, ∀ θ ∈ Icc (min α β) (max α β),
      o + ρ • direction θ ∈
        convexHull ℝ ({o + r • direction α, o, o + s • direction β} : Set Plane) := by
  rcases lt_or_gt_of_ne different with before | after
  · obtain ⟨ε, ep, inside⟩ := translated_triangle_small_sector o r s α β rp sp before
      (by rwa [abs_of_pos (sub_pos.mpr before)] at short)
    refine ⟨ε, ep, ?_⟩
    intro ρ hr θ hθ
    simpa only [Set.insert_comm] using inside ρ hr θ (by simpa [min_eq_left before.le, max_eq_right before.le] using hθ)
  · obtain ⟨ε, ep, inside⟩ := translated_triangle_small_sector o s r β α sp rp after
      (by rw [abs_of_neg (sub_neg.mpr after)] at short; linarith)
    refine ⟨ε, ep, ?_⟩
    intro ρ hr θ hθ
    have member := inside ρ hr θ (by simpa [min_eq_right after.le, max_eq_left after.le] using hθ)
    have same : ({o, o + s • direction β, o + r • direction α} : Set Plane) =
        {o + r • direction α, o, o + s • direction β} := by
      ext x
      simp only [mem_insert_iff, mem_singleton_iff]
      tauto
    rwa [same] at member

end SixVertexUnfolding
