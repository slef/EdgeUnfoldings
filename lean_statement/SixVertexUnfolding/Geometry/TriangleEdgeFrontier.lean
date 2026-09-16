import SixVertexUnfolding.Geometry.JoinedTriangleFrontier

/-! Every closed side of a nondegenerate planar triangle belongs to its frontier. -/

namespace SixVertexUnfolding

/-- A zero displacement has zero signed area. -/
theorem det_zero_right (v : Plane) : det v 0 = 0 := by simp [det]

/-- Reversing the base reverses its signed height. -/
theorem triangle_area_reverse_base (a b x : Plane) :
    det (a - b) (x - b) = -det (b - a) (x - a) := by
  simp only [det, PiLp.sub_apply]
  ring

/-- An edge has zero height, whereas interior points have strictly positive height. -/
theorem positive_triangle_base_subset_frontier (a b c : Plane)
    (positive : 0 < det (b - a) (c - a)) :
    segment ℝ a b ⊆ frontier (convexHull ℝ ({a, b, c} : Set Plane)) := by
  let height := detHeight (b - a)
  have onto : Function.Surjective height := by
    intro r
    refine ⟨(r / det (b - a) (c - a)) • (c - a), ?_⟩
    change det (b - a) ((r / det (b - a) (c - a)) • (c - a)) = r
    rw [det_smul_right]
    exact div_mul_cancel₀ r positive.ne'
  have bound : convexHull ℝ ({a, b, c} : Set Plane) ⊆ height ⁻¹' Set.Ici (height a) := by
    intro x member
    have side := triangle_base_height_nonneg a b c x positive.le member
    rw [det_sub_right] at side
    change det (b - a) a ≤ det (b - a) x
    linarith
  have strict := interior_mono bound
  rw [height.interior_preimage onto, interior_Ici] at strict
  rintro x ⟨s, t, hs, ht, total, expression⟩
  apply (mem_frontier_iff_notMem_interior ((convex_convexHull ℝ _).segment_subset
    (subset_convexHull ℝ _ (by simp)) (subset_convexHull ℝ _ (by simp))
    (show x ∈ segment ℝ a b from ⟨s, t, hs, ht, total, expression⟩))).mpr
  intro inside
  have above := strict inside
  change det (b - a) a < det (b - a) x at above
  have on_line := segment_weighted_area a b a b x s t total expression
  simp only [sub_self, det_zero_right, det_self, mul_zero, add_zero, det_sub_right] at on_line
  linarith

/-- Either orientation gives the same whole-edge frontier statement. -/
theorem triangle_base_subset_frontier (a b c : Plane)
    (nonzero : det (b - a) (c - a) ≠ 0) :
    segment ℝ a b ⊆ frontier (convexHull ℝ ({a, b, c} : Set Plane)) := by
  rcases lt_or_gt_of_ne nonzero with negative | positive
  · have reversed : 0 < det (a - b) (c - b) := by
      rw [triangle_area_reverse_base]
      exact neg_pos.mpr negative
    simpa only [segment_symm ℝ b a, Set.insert_comm] using positive_triangle_base_subset_frontier b a c reversed
  · exact positive_triangle_base_subset_frontier a b c positive

end SixVertexUnfolding
