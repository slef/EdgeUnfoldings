import SixVertexUnfolding.Geometry.CutLineArcs

/-! An explicit affine, unit-speed parametrization of a planar line. -/

namespace SixVertexUnfolding

open Set

theorem plane_line_parametrization (normal : Plane) (nonzero : normal ≠ 0)
    (level : ℝ) (origin : Plane) (on_line : inner ℝ normal origin = level) :
    ∃ line : ℝ →ᵃ[ℝ] Plane, Isometry line ∧ range line = {x | inner ℝ normal x = level} := by
  obtain ⟨d, unit, perpendicular⟩ := plane_unit_perpendicular normal nonzero
  let line : ℝ →ᵃ[ℝ] Plane := AffineMap.lineMap origin (origin + d)
  have formula (t : ℝ) : line t = origin + t • d := by
    rw [AffineMap.lineMap_apply_module]
    module
  refine ⟨line, Isometry.of_dist_eq ?_, ?_⟩
  · intro s t
    rw [dist_eq_norm, formula s, formula t,
      show origin + s • d - (origin + t • d) = (s - t) • d by module,
      norm_smul, unit, mul_one, Real.norm_eq_abs, Real.dist_eq]
  · ext x
    constructor
    · rintro ⟨t, rfl⟩
      simp only [mem_setOf_eq, formula, inner_add_right, inner_smul_right,
        perpendicular, mul_zero, add_zero, on_line]
    · intro hx
      have orthogonal : inner ℝ normal (x - origin) = 0 := by
        rw [inner_sub_right, hx, on_line, sub_self]
      have d_ne : d ≠ 0 := by intro zero; simp [zero] at unit
      obtain ⟨t, same⟩ := perpendicular_multiple normal d (x - origin) nonzero d_ne perpendicular orthogonal
      exact ⟨t, by rw [formula, ← same]; module⟩

end SixVertexUnfolding
