import SixVertexUnfolding.Geometry.HingeUniqueness

/-! Ordering and uniqueness on the two sides of a planar hinge. -/

namespace SixVertexUnfolding

/-- In the plane, every vector perpendicular to an axis is a multiple of any nonzero perpendicular vector. -/
theorem perpendicular_multiple (axis n x : Plane) (axis_ne : axis ≠ 0) (n_ne : n ≠ 0)
    (n_orthogonal : inner ℝ axis n = 0) (x_orthogonal : inner ℝ axis x = 0) :
    ∃ t : ℝ, x = t • n := by
  let D := (Submodule.span ℝ ({axis} : Set Plane))ᗮ
  have dimension : Module.finrank ℝ D = 1 := by
    have sum := (Submodule.span ℝ ({axis} : Set Plane)).finrank_add_finrank_orthogonal
    rw [finrank_span_singleton axis_ne] at sum
    have ambient : Module.finrank ℝ Plane = 2 := by simp [Plane]
    rw [ambient] at sum
    change 1 + Module.finrank ℝ D = 2 at sum
    omega
  have n_mem : n ∈ D := Submodule.mem_orthogonal_singleton_iff_inner_right.mpr n_orthogonal
  have x_mem : x ∈ D := Submodule.mem_orthogonal_singleton_iff_inner_right.mpr x_orthogonal
  obtain ⟨t, equal⟩ := exists_smul_eq_of_finrank_eq_one dimension
    (show (⟨n, n_mem⟩ : D) ≠ 0 from fun same => n_ne (congrArg Subtype.val same)) (⟨x, x_mem⟩ : D)
  exact ⟨t, (congrArg Subtype.val equal).symm⟩

/-- Two points opposite the same noncollinear reference lie on the same closed hinge side. -/
theorem same_side_of_opposite (a b reference x y : Plane)
    (noncollinear : ¬ Collinear ℝ ({a, b, reference} : Set Plane))
    (left : OppositeHingeSides a b reference x) (right : OppositeHingeSides a b reference y) :
    0 ≤ inner ℝ (hingeSideVector a b x) (hingeSideVector a b y) := by
  have ab : a ≠ b := by
    intro same
    apply noncollinear
    simpa [same] using collinear_pair ℝ b reference
  let axis := NormedSpace.normalize (b - a)
  have unit : ‖axis‖ = 1 := NormedSpace.norm_normalize (sub_ne_zero.mpr ab.symm)
  have axis_ne : axis ≠ 0 := by intro zero; simp [zero] at unit
  let n := hingeSideVector a b reference
  have n_ne : n ≠ 0 := hingeSideVector_ne_zero a b reference noncollinear
  have orthogonal (z : Plane) : inner ℝ axis (hingeSideVector a b z) = 0 :=
    hingeRemainder_orthogonal unit (z - a)
  obtain ⟨s, x_eq⟩ := perpendicular_multiple axis n (hingeSideVector a b x) axis_ne n_ne (orthogonal reference) (orthogonal x)
  obtain ⟨t, y_eq⟩ := perpendicular_multiple axis n (hingeSideVector a b y) axis_ne n_ne (orthogonal reference) (orthogonal y)
  change inner ℝ n (hingeSideVector a b x) ≤ 0 at left
  change inner ℝ n (hingeSideVector a b y) ≤ 0 at right
  rw [x_eq, inner_smul_right, real_inner_self_eq_norm_sq] at left
  rw [y_eq, inner_smul_right, real_inner_self_eq_norm_sq] at right
  have norm_pos : 0 < ‖n‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr n_ne)
  have s_nonpos : s ≤ 0 := by nlinarith
  have t_nonpos : t ≤ 0 := by nlinarith
  rw [x_eq, y_eq, real_inner_smul_left, inner_smul_right, real_inner_self_eq_norm_sq]
  nlinarith [mul_nonneg (mul_nonneg_of_nonpos_of_nonpos s_nonpos t_nonpos) norm_pos.le]

/-- Distances and an outward-side requirement uniquely fix the new triangle corner. -/
theorem outward_point_unique (a b reference x y : Plane)
    (noncollinear : ¬ Collinear ℝ ({a, b, reference} : Set Plane))
    (at_a : dist a x = dist a y) (at_b : dist b x = dist b y)
    (left : OppositeHingeSides a b reference x) (right : OppositeHingeSides a b reference y) : x = y := by
  have ab : a ≠ b := by
    intro same
    apply noncollinear
    simpa [same] using collinear_pair ℝ b reference
  exact point_eq_of_hinge_distances a b x y ab at_a at_b (same_side_of_opposite a b reference x y noncollinear left right)

theorem hingeRemainder_neg_axis (axis x : Plane) : hingeRemainder (-axis) x = hingeRemainder axis x := by
  simp [hingeRemainder]

theorem hingeRemainder_sub (axis x y : Plane) : hingeRemainder axis (x - y) =
    hingeRemainder axis x - hingeRemainder axis y := by
  simp only [hingeRemainder, inner_sub_right, sub_smul]
  module

/-- Reversing the hinge's endpoints does not change its perpendicular component. -/
theorem hingeSideVector_swap (a b x : Plane) (ab : a ≠ b) : hingeSideVector b a x = hingeSideVector a b x := by
  have axis : NormedSpace.normalize (a - b) = -NormedSpace.normalize (b - a) := by
    calc
      NormedSpace.normalize (a - b) = NormedSpace.normalize (-(b - a)) := by congr 1; module
      _ = -NormedSpace.normalize (b - a) := NormedSpace.normalize_neg _
  have difference : x - b = (x - a) - (b - a) := by module
  rw [hingeSideVector, axis, hingeRemainder_neg_axis, difference, hingeRemainder_sub]
  change hingeSideVector a b x - hingeSideVector a b b = hingeSideVector a b x
  rw [hingeSideVector_right a b ab, sub_zero]

theorem oppositeHingeSides_swap (a b x y : Plane) (ab : a ≠ b) :
    OppositeHingeSides b a x y ↔ OppositeHingeSides a b x y := by
  simp only [OppositeHingeSides, hingeSideVector_swap a b _ ab]

end SixVertexUnfolding
