import SixVertexUnfolding.Geometry.PlanarRayTriangle
import SixVertexUnfolding.Geometry.OutwardTriangle

/-! A fan triangle and its outward petal occupy a common open half-plane as seen from the fan pole. -/

namespace SixVertexUnfolding

open InnerProductGeometry

/-- A nonzero point in the hull of the origin and a triangle is on a positive ray through that triangle. -/
theorem zero_triangle_hull_ray (point : Fin 3 → Plane) (x : Plane) (nonzero : x ≠ 0)
    (member : x ∈ convexHull ℝ (insert 0 (Set.range point))) :
    ∃ (t : ℝ) (z : Plane), 0 < t ∧ z ∈ convexHull ℝ (Set.range point) ∧ x = t • z := by
  rw [convexHull_insert (Set.range_nonempty point)] at member
  obtain ⟨a, ha, z, hz, between⟩ := mem_convexJoin.mp member
  have same : a = 0 := ha
  subst a
  obtain ⟨s, t, hs, ht, total, expression⟩ := between
  simp only [smul_zero, zero_add] at expression
  have positive : 0 < t := by
    apply lt_of_le_of_ne ht
    intro zero
    apply nonzero
    rw [← expression, ← zero, zero_smul]
  exact ⟨t, z, positive, hz, expression.symm⟩

/-- Corner-ray bounds control the whole hull of a patch, apart from its viewing pole itself. -/
theorem zero_triangle_hull_angular_bound (height : Plane →ₗ[ℝ] ℝ) (point : Fin 3 → Plane) (bound : ℝ)
    (positive : ∀ i, 0 < height (point i))
    (corners : ∀ i j, angle (point i) (point j) < bound)
    (x y : Plane) (hx : x ∈ convexHull ℝ (insert 0 (Set.range point)))
    (hy : y ∈ convexHull ℝ (insert 0 (Set.range point))) (x_ne : x ≠ 0) (y_ne : y ≠ 0) :
    angle x y < bound := by
  obtain ⟨s, a, hs, ha, rfl⟩ := zero_triangle_hull_ray point x x_ne hx
  obtain ⟨t, b, ht, hb, rfl⟩ := zero_triangle_hull_ray point y y_ne hy
  rw [angle_smul_left_of_pos _ _ hs, angle_smul_right_of_pos _ _ ht]
  exact triangle_angular_bound height point bound positive corners a b ha hb

/-- The three outgoing corner rays of an outward patch have strictly positive common height. -/
theorem outward_patch_height (a b w v : Plane)
    (noncollinear : ¬ Collinear ℝ ({a, b, w} : Set Plane))
    (outward : OppositeHingeSides a b w v) :
    ∃ height : Plane →ₗ[ℝ] ℝ,
      0 < height (a - w) ∧ 0 < height (b - w) ∧ 0 < height (v - w) := by
  have ab : a ≠ b := by
    intro same
    apply noncollinear
    simpa [same] using collinear_pair ℝ b w
  let n := hingeSideVector a b w
  have n_ne : n ≠ 0 := hingeSideVector_ne_zero a b w noncollinear
  have pole_height : 0 < inner ℝ n (w - a) := by
    rw [hingeSideVector_inner a b w w ab]
    change 0 < inner ℝ n n
    rw [real_inner_self_eq_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr n_ne)
  have hinge_height : inner ℝ n (b - a) = 0 := by
    rw [hingeSideVector_inner a b w b ab, hingeSideVector_right a b ab, inner_zero_right]
  have petal_height : inner ℝ n (v - a) ≤ 0 := by
    rw [hingeSideVector_inner a b w v ab]
    exact outward
  refine ⟨(innerSL ℝ (-n)).toLinearMap, ?_, ?_, ?_⟩ <;>
    change 0 < inner ℝ (-n) _ <;>
    simp only [inner_neg_left, inner_sub_right] at * <;> linarith

end SixVertexUnfolding
