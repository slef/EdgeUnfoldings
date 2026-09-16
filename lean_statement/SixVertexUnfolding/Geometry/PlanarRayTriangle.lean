import SixVertexUnfolding.Geometry.AngularSegment
import SixVertexUnfolding.Geometry.TriangleTopology
import SixVertexUnfolding.Geometry.TriangleWeights

/-! Angular bounds at three planar rays extend to their entire positive hull. -/

namespace SixVertexUnfolding

open InnerProductGeometry

/-- Three planar points on the transverse line `height = 1` are collinear. -/
theorem height_one_collinear (height : Plane →ₗ[ℝ] ℝ) (a b c : Plane)
    (ha : height a = 1) (hb : height b = 1) (hc : height c = 1) :
    Collinear ℝ ({a, b, c} : Set Plane) := by
  by_contra noncollinear
  let line := (affineSpan ℝ ({(1 : ℝ)} : Set ℝ)).comap height.toAffineMap
  have on_line : ({a, b, c} : Set Plane) ⊆ line := by
    rintro x (rfl | rfl | rfl) <;> simpa [line] using (by assumption : height x = 1)
  have contains_plane : (⊤ : AffineSubspace ℝ Plane) ≤ line := by
    rw [← planar_triangle_spans a b c noncollinear]
    exact affineSpan_le.mpr on_line
  have zero := contains_plane (show (0 : Plane) ∈ (⊤ : AffineSubspace ℝ Plane) from trivial)
  simpa [line] using zero

/-- A collinear third point adds nothing beyond the segment containing it. -/
theorem triangle_hull_eq_segment (a b c : Plane) (between : b ∈ segment ℝ a c) :
    convexHull ℝ ({a, b, c} : Set Plane) = segment ℝ a c := by
  apply Set.Subset.antisymm
  · apply convexHull_min _ (convex_segment a c)
    rintro x (rfl | rfl | rfl)
    exacts [left_mem_segment ℝ _ _, between, right_mem_segment ℝ _ _]
  · rw [← convexHull_pair]
    apply convexHull_mono
    intro x member
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at member ⊢
    tauto

/-- The hull of three points on a transverse line has two of those points as endpoints. -/
theorem height_one_hull_is_segment (height : Plane →ₗ[ℝ] ℝ) (point : Fin 3 → Plane)
    (level : ∀ i, height (point i) = 1) :
    ∃ i j, convexHull ℝ (Set.range point) = segment ℝ (point i) (point j) := by
  have points : Set.range point = ({point 0, point 1, point 2} : Set Plane) := by
    ext x
    simp [Set.mem_range, Fin.exists_fin_succ, eq_comm]
  rw [points]
  have collinear := height_one_collinear height (point 0) (point 1) (point 2) (level 0) (level 1) (level 2)
  rcases collinear.wbtw_or_wbtw_or_wbtw with middle | last | first
  · exact ⟨0, 2, triangle_hull_eq_segment _ _ _ (mem_segment_iff_wbtw.mpr middle)⟩
  · refine ⟨1, 0, ?_⟩
    have reorder : ({point 0, point 1, point 2} : Set Plane) = {point 1, point 2, point 0} := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [reorder]
    exact triangle_hull_eq_segment _ _ _ (mem_segment_iff_wbtw.mpr last)
  · refine ⟨2, 1, ?_⟩
    have reorder : ({point 0, point 1, point 2} : Set Plane) = {point 2, point 0, point 1} := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [reorder]
    exact triangle_hull_eq_segment _ _ _ (mem_segment_iff_wbtw.mpr first)

/-- Intersect a positive ray with the transverse line. -/
noncomputable def heightNormalize (height : Plane →ₗ[ℝ] ℝ) (x : Plane) : Plane :=
  (height x)⁻¹ • x

theorem heightNormalize_level (height : Plane →ₗ[ℝ] ℝ) (x : Plane) (positive : 0 < height x) :
    height (heightNormalize height x) = 1 := by
  simp [heightNormalize, ne_of_gt positive]

theorem heightNormalize_angle (height : Plane →ₗ[ℝ] ℝ) (x y : Plane)
    (hx : 0 < height x) (hy : 0 < height y) :
    angle (heightNormalize height x) (heightNormalize height y) = angle x y := by
  rw [heightNormalize, heightNormalize, angle_smul_left_of_pos _ _ (inv_pos.mpr hx),
    angle_smul_right_of_pos _ _ (inv_pos.mpr hy)]

/-- Every point in a positive-height triangle has positive height. -/
theorem triangle_height_pos (height : Plane →ₗ[ℝ] ℝ) (a b c x : Plane)
    (ha : 0 < height a) (hb : 0 < height b) (hc : 0 < height c)
    (member : x ∈ convexHull ℝ ({a, b, c} : Set Plane)) : 0 < height x := by
  have contained : convexHull ℝ ({a, b, c} : Set Plane) ⊆ {z | 0 < height z} := by
    apply convexHull_min _ (convex_halfSpace_gt
      ⟨fun x y => height.map_add x y, fun r x => height.map_smul r x⟩ 0)
    rintro z (rfl | rfl | rfl)
    exacts [ha, hb, hc]
  exact contained member

/-- Radial projection preserves membership in the triangle of the projected rays. -/
theorem heightNormalize_mem_triangle (height : Plane →ₗ[ℝ] ℝ) (a b c x : Plane)
    (ha : 0 < height a) (hb : 0 < height b) (hc : 0 < height c)
    (member : x ∈ convexHull ℝ ({a, b, c} : Set Plane)) :
    heightNormalize height x ∈ convexHull ℝ
      ({heightNormalize height a, heightNormalize height b, heightNormalize height c} : Set Plane) := by
  obtain ⟨s, t, u, hs, ht, hu, total, expression⟩ := triangle_weights a b c x member
  have hx := triangle_height_pos height a b c x ha hb hc member
  have height_sum : s * height a + t * height b + u * height c = height x := by
    simpa only [map_add, map_smul, smul_eq_mul] using congrArg height expression
  have weights : s * height a / height x + t * height b / height x + u * height c / height x = 1 := by
    rw [← add_div, ← add_div, height_sum, div_self (ne_of_gt hx)]
  have combination : (s * height a / height x) • heightNormalize height a +
      (t * height b / height x) • heightNormalize height b +
      (u * height c / height x) • heightNormalize height c = heightNormalize height x := by
    simp only [heightNormalize, smul_smul]
    have cancel (r z : ℝ) (hz : z ≠ 0) : (r * z / height x) * z⁻¹ = (height x)⁻¹ * r := by
      field_simp
    rw [cancel s _ (ne_of_gt ha), cancel t _ (ne_of_gt hb), cancel u _ (ne_of_gt hc),
      mul_smul, mul_smul, mul_smul, ← smul_add, ← smul_add, expression]
  rw [← combination]
  let weight : Fin 3 → ℝ := ![s * height a / height x, t * height b / height x, u * height c / height x]
  let point : Fin 3 → Plane := ![heightNormalize height a, heightNormalize height b, heightNormalize height c]
  have combination_mem := (convex_convexHull ℝ
    ({heightNormalize height a, heightNormalize height b, heightNormalize height c} : Set Plane)).sum_mem
    (t := Finset.univ) (w := weight) (z := point)
    (by intro i _; fin_cases i <;> dsimp [weight] <;> positivity)
    (by simpa [weight, Fin.sum_univ_three] using weights)
    (by intro i _; apply subset_convexHull ℝ _; fin_cases i <;> simp [point])
  simpa only [Fin.sum_univ_three, weight, point, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two] using combination_mem

/-- For rays in one open planar half-plane, the angular diameter is attained at two corner rays. -/
theorem triangle_angular_bound (height : Plane →ₗ[ℝ] ℝ) (point : Fin 3 → Plane) (bound : ℝ)
    (positive : ∀ i, 0 < height (point i))
    (corners : ∀ i j, angle (point i) (point j) < bound)
    (x y : Plane) (hx : x ∈ convexHull ℝ (Set.range point))
    (hy : y ∈ convexHull ℝ (Set.range point)) : angle x y < bound := by
  have range_three (f : Fin 3 → Plane) : Set.range f = ({f 0, f 1, f 2} : Set Plane) := by
    ext z
    simp [Set.mem_range, Fin.exists_fin_succ, eq_comm]
  let projected := fun i => heightNormalize height (point i)
  obtain ⟨i, j, endpoints⟩ := height_one_hull_is_segment height projected
    (fun k => heightNormalize_level height _ (positive k))
  have project_member (z : Plane) (member : z ∈ convexHull ℝ (Set.range point)) :
      0 < height z ∧ heightNormalize height z ∈ segment ℝ (projected i) (projected j) := by
    rw [range_three] at member
    refine ⟨triangle_height_pos height _ _ _ z (positive 0) (positive 1) (positive 2) member, ?_⟩
    rw [← endpoints, range_three]
    exact heightNormalize_mem_triangle height _ _ _ z (positive 0) (positive 1) (positive 2) member
  obtain ⟨x_pos, x_between⟩ := project_member x hx
  obtain ⟨y_pos, y_between⟩ := project_member y hy
  have comparison := angle_le_of_segment_points height (projected i) (projected j)
    (heightNormalize height x) (heightNormalize height y)
    (by rw [heightNormalize_level height _ (positive i)]; norm_num)
    (by rw [heightNormalize_level height _ (positive j)]; norm_num)
    x_between y_between
  change angle (heightNormalize height x) (heightNormalize height y) ≤
    angle (heightNormalize height (point i)) (heightNormalize height (point j)) at comparison
  rw [heightNormalize_angle height x y x_pos y_pos,
    heightNormalize_angle height _ _ (positive i) (positive j)] at comparison
  exact lt_of_le_of_lt comparison (corners i j)

end SixVertexUnfolding
