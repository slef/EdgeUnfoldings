import SixVertexUnfolding.Geometry.MetricSegmentCoordinates

/-! A later point of a parametrized straight route determines its earlier
position once the common source and target are fixed. -/

namespace SixVertexUnfolding

/-- Recover an earlier position from one later terminal interpolation. -/
theorem terminal_interpolation_unique (source target position : Plane) (t u : ℝ)
    (before : t < 1) (u_before : u < 1)
    (equal : AffineMap.lineMap position target ((u - t) / (1 - t)) = AffineMap.lineMap source target u) :
    position = AffineMap.lineMap source target t := by
  have nonzero : 1 - t ≠ 0 := ne_of_gt (sub_pos.mpr before)
  let r := (u - t) / (1 - t)
  have r_before : r < 1 := (div_lt_one (sub_pos.mpr before)).mpr (sub_lt_sub_right u_before _)
  have coefficient : (1 - r) * (1 - t) = 1 - u := by dsimp [r]; field_simp [nonzero]; ring
  have second_coefficient : (1 - r) * t + r = u := by dsimp [r]; field_simp [nonzero]; ring
  have nested : AffineMap.lineMap (AffineMap.lineMap source target t) target r = AffineMap.lineMap source target u := by
    simp only [AffineMap.lineMap_apply_module, smul_add, smul_smul]
    rw [add_assoc, ← add_smul, coefficient, second_coefficient]
  exact lineMap_left_unique position _ target r r_before.ne (equal.trans nested.symm)

end SixVertexUnfolding
