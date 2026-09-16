import SixVertexUnfolding.Geometry.TriangleMetricComparison

/-! A genuinely spatial pair of triangles has a strict free-vertex distance increase. -/

namespace SixVertexUnfolding

theorem normalized_hinge_in_direction (s : Set Space) (a b : Space) (ha : a ∈ s) (hb : b ∈ s) :
    NormedSpace.normalize (b - a) ∈ (affineSpan ℝ s).direction := by
  apply Submodule.smul_mem
  exact AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ _ hb) (subset_affineSpan ℝ _ ha)

theorem noncoplanar_hinge_components (a b x y : Space)
    (noncollinear : ¬ Collinear ℝ ({a, b, x} : Set Space))
    (noncoplanar : y ∉ affineSpan ℝ ({a, b, x} : Set Space)) :
    (x - a) ∉ Submodule.span ℝ ({NormedSpace.normalize (b - a)} : Set Space) ∧
    (y - a) ∉ Submodule.span ℝ ({NormedSpace.normalize (b - a), x - a} : Set Space) := by
  constructor
  · intro member
    have inclusion : Submodule.span ℝ ({NormedSpace.normalize (b - a)} : Set Space) ≤
        (affineSpan ℝ ({a, b} : Set Space)).direction :=
      Submodule.span_le.mpr (Set.singleton_subset_iff.mpr
        (normalized_hinge_in_direction {a, b} a b (by simp) (by simp)))
    have x_in : x ∈ affineSpan ℝ ({a, b} : Set Space) := by
      simpa using AffineSubspace.vadd_mem_of_mem_direction (inclusion member)
        (left_mem_affineSpan_pair ℝ a b)
    exact noncollinear (collinear_triple_of_mem_affineSpan_pair
      (left_mem_affineSpan_pair ℝ a b) (right_mem_affineSpan_pair ℝ a b) x_in)
  · intro member
    have inclusion : Submodule.span ℝ ({NormedSpace.normalize (b - a), x - a} : Set Space) ≤
        (affineSpan ℝ ({a, b, x} : Set Space)).direction := by
      apply Submodule.span_le.mpr
      rintro z (rfl | rfl)
      · exact normalized_hinge_in_direction {a, b, x} a b (by simp) (by simp)
      · exact AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ _ (by simp))
          (subset_affineSpan ℝ _ (by simp))
    apply noncoplanar
    simpa using AffineSubspace.vadd_mem_of_mem_direction (inclusion member)
      (subset_affineSpan ℝ ({a, b, x} : Set Space) (by simp : a ∈ ({a, b, x} : Set Space)))

/-- Noncoplanar triangles become strictly farther apart at their free vertices when flattened outward. -/
theorem two_triangles_distance_gt (a b x y : Space) (A B X Y : Plane) (distinct : a ≠ b)
    (ab : dist A B = dist a b)
    (ax : dist A X = dist a x) (bx : dist B X = dist b x)
    (ay : dist A Y = dist a y) (by_ : dist B Y = dist b y)
    (opposite : OppositeHingeSides A B X Y)
    (noncollinear : ¬ Collinear ℝ ({a, b, x} : Set Space))
    (noncoplanar : y ∉ affineSpan ℝ ({a, b, x} : Set Space)) : dist x y < dist X Y := by
  have AB : A ≠ B := by intro same; have := ab; simp [same] at this; exact distinct this
  have x_length : ‖X - A‖ = ‖x - a‖ := by simpa only [dist_eq_norm, norm_sub_rev] using ax
  have y_length : ‖Y - A‖ = ‖y - a‖ := by simpa only [dist_eq_norm, norm_sub_rev] using ay
  have independent := noncoplanar_hinge_components a b x y noncollinear noncoplanar
  have strict := opposite_flattening_inner_lt
    (NormedSpace.normalize (b - a)) (NormedSpace.normalize (B - A))
    (NormedSpace.norm_normalize (sub_ne_zero.mpr distinct.symm))
    (NormedSpace.norm_normalize (sub_ne_zero.mpr AB.symm))
    (x - a) (y - a) (X - A) (Y - A) x_length y_length
    (triangle_hinge_component_of_distances a b x A B X ab ax bx)
    (triangle_hinge_component_of_distances a b y A B Y ab ay by_)
    opposite independent.1 independent.2
  have original := norm_sub_sq_real (x - a) (y - a)
  have placed := norm_sub_sq_real (X - A) (Y - A)
  simp only [sub_sub_sub_cancel_right] at original placed
  rw [x_length, y_length] at placed
  rw [dist_eq_norm, dist_eq_norm]
  apply (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  linarith

end SixVertexUnfolding
