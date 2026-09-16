import SixVertexUnfolding.Geometry.TriangleFanParameters
import Mathlib.Analysis.Normed.Affine.AddTorsorBases

/-! A radial triangle point is in its ordinary planar interior exactly
when both its base parameter and its route parameter are strictly interior. -/

namespace SixVertexUnfolding

open Set

/-- Strict radial parameters correspond exactly to the triangle's two-dimensional interior. -/
theorem triangleFan_interior_iff (p u v : Plane)
    (noncollinear : ¬ Collinear ℝ ({p, u, v} : Set Plane)) (z : unitInterval × unitInterval) :
    triangleFanMap p u v z ∈ interior (convexHull ℝ ({p, u, v} : Set Plane)) ↔
      0 < (z.1 : ℝ) ∧ (z.1 : ℝ) < 1 ∧ 0 < (z.2 : ℝ) ∧ (z.2 : ℝ) < 1 := by
  have independent : AffineIndependent ℝ ![p, u, v] :=
    affineIndependent_iff_not_collinear_set.mpr noncollinear
  let basis : AffineBasis (Fin 3) ℝ Plane := {
    toFun := ![p, u, v]
    ind' := independent
    tot' := independent.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp [Plane]) }
  have vertices : range basis = ({p, u, v} : Set Plane) := by
    change range ![p, u, v] = _
    ext x; simp [Matrix.range_cons, Matrix.range_empty]; tauto
  have first : basis.coord 0 (triangleFanMap p u v z) = 1 - (z.2 : ℝ) := by
    change basis.coord 0 (AffineMap.lineMap (basis 0)
      (AffineMap.lineMap (basis 1) (basis 2) (z.1 : ℝ)) (z.2 : ℝ)) = _
    rw [AffineMap.apply_lineMap, AffineMap.apply_lineMap]
    simp [AffineMap.lineMap_apply_module]
  have second : basis.coord 1 (triangleFanMap p u v z) = (z.2 : ℝ) * (1 - (z.1 : ℝ)) := by
    change basis.coord 1 (AffineMap.lineMap (basis 0)
      (AffineMap.lineMap (basis 1) (basis 2) (z.1 : ℝ)) (z.2 : ℝ)) = _
    rw [AffineMap.apply_lineMap, AffineMap.apply_lineMap]
    simp [AffineMap.lineMap_apply_module]
  have third : basis.coord 2 (triangleFanMap p u v z) = (z.2 : ℝ) * (z.1 : ℝ) := by
    change basis.coord 2 (AffineMap.lineMap (basis 0)
      (AffineMap.lineMap (basis 1) (basis 2) (z.1 : ℝ)) (z.2 : ℝ)) = _
    rw [AffineMap.apply_lineMap, AffineMap.apply_lineMap]
    simp [AffineMap.lineMap_apply_module]
  rw [← vertices, basis.interior_convexHull]
  change (∀ i, 0 < basis.coord i (triangleFanMap p u v z)) ↔ _
  constructor
  · intro all
    have h₀ := all 0
    have h₁ := all 1
    have h₂ := all 2
    rw [first] at h₀
    rw [second] at h₁
    rw [third] at h₂
    have s_positive : 0 < (z.2 : ℝ) := by nlinarith [z.1.property.1, z.1.property.2, z.2.property.1]
    have t_positive : 0 < (z.1 : ℝ) := by nlinarith [z.1.property.1, z.2.property.2]
    have t_before : (z.1 : ℝ) < 1 := by nlinarith [z.1.property.2]
    exact ⟨t_positive, t_before, s_positive, by linarith⟩
  · rintro ⟨t_positive, t_before, s_positive, s_before⟩
    intro i
    fin_cases i
    · change 0 < basis.coord 0 (triangleFanMap p u v z)
      rw [first]; exact sub_pos.mpr s_before
    · change 0 < basis.coord 1 (triangleFanMap p u v z)
      rw [second]; exact mul_pos s_positive (sub_pos.mpr t_before)
    · change 0 < basis.coord 2 (triangleFanMap p u v z)
      rw [third]; exact mul_pos s_positive t_positive

end SixVertexUnfolding
