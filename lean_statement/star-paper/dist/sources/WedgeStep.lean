import SixVertexUnfolding.Geometry.WedgeCoordinates

/-! One complete planar wedge step: rotate the arms, add the next kite,
and express the result as a wedge about the new root. The hypotheses state
the angular order and the angle budget; the cut-surface construction must
still supply those facts at actual tree junctions.
-/

namespace SixVertexUnfolding.Wedge

open Real Set

/-- Scaling a ray's direction by a positive number does not change the region. -/
theorem region_rescale (h r a b : ℝ) {c : ℝ} (positive : 0 < c) :
    region h r (c * a) (c * b) = region h r a b := by
  have negative : c * a < 0 ↔ a < 0 := by
    simpa using (mul_lt_mul_iff_right₀ positive : c * a < c * 0 ↔ a < 0)
  ext z
  simp only [region, mem_setOf_eq, mul_assoc, mul_pos_iff_of_pos_left positive,
    mul_nonneg_iff_of_pos_left positive, negative,
    mul_le_mul_iff_right₀ positive]

namespace ArmCoordinates

variable {h r a b d θ γ : ℝ} (C : ArmCoordinates h r a b d θ γ)
include C

/-- The source direction increases when the root moves to the right. -/
theorem source_direction_mono {q D Θ : ℝ} (order : r ≤ q) (radius : 0 < D)
    (angle_pos : 0 < Θ)
    (source_x : -q = D * cos Θ) (source_y : h = D * sin Θ) : θ ≤ Θ := by
  have product : d * D * sin (Θ - θ) = h * (q - r) := by
    rw [sin_sub]
    rw [C.source_y, show r = -(d * cos θ) by linarith [C.source_x],
      show q = -(D * cos Θ) by linarith [source_x]]
    have heights : d * sin θ = D * sin Θ := C.source_y.symm.trans source_y
    nlinarith [congrArg (fun x : ℝ => d * cos θ * x) heights]
  have sine : 0 ≤ sin (Θ - θ) := by
    have nonnegative := mul_nonneg C.height_pos.le (sub_nonneg.mpr order)
    rw [← product] at nonnegative
    exact (mul_nonneg_iff_of_pos_left (mul_pos C.radius_pos radius)).mp nonnegative
  by_contra backwards
  have negative := sin_neg_of_neg_of_neg_pi_lt (by linarith : Θ - θ < 0)
    (by linarith [C.angle_lt_pi] : -π < Θ - θ)
  linarith

/-- The same outer rays, seen from the new root, have angle `γ + (Θ - θ)`.
Their directions are rescaled only to match the new inner-leg length. -/
theorem moved_coordinates {q D Θ : ℝ} (radius : 0 < D)
    (angle_pos : 0 < Θ) (angle_lt_pi : Θ < π)
    (source_x : -q = D * cos Θ) (source_y : h = D * sin Θ)
    (lower : π / 2 ≤ γ + (Θ - θ)) (upper : γ + (Θ - θ) ≤ 3 * π / 2) :
    ArmCoordinates h q (D / d * a) (D / d * b) D Θ (γ + (Θ - θ)) := by
  refine ⟨radius, angle_pos, angle_lt_pi, lower, upper, source_x, source_y, ?_, ?_⟩
  · rw [show Θ + (π - (γ + (Θ - θ))) = θ + (π - γ) by ring, C.ray_x]
    field_simp [ne_of_gt C.radius_pos]
  · rw [show Θ + (π - (γ + (Θ - θ))) = θ + (π - γ) by ring, C.ray_y]
    field_simp [ne_of_gt C.radius_pos]

/-- The new angle bound supplies the second outward condition in `root_step`. -/
theorem next_outward {q D Θ : ℝ} (radius : 0 < D)
    (angle_pos : 0 < Θ) (angle_lt_pi : Θ < π)
    (source_x : -q = D * cos Θ) (source_y : h = D * sin Θ)
    (lower : π / 2 ≤ γ + (Θ - θ)) (upper : γ + (Θ - θ) ≤ 3 * π / 2) :
    0 ≤ h * b - q * a := by
  have next := (C.moved_coordinates radius angle_pos angle_lt_pi source_x source_y lower upper).outward
  have positive := div_pos radius C.radius_pos
  have factored : 0 ≤ D / d * (h * b - q * a) := by nlinarith [next]
  exact (mul_nonneg_iff_of_pos_left positive).mp factored

/-- The angle increase is the ordinary angle at the upper apex of the kite. -/
theorem kite_apex_angle {q D Θ : ℝ} (order : r ≤ q) (radius : 0 < D)
    (angle_pos : 0 < Θ) (angle_lt_pi : Θ < π)
    (source_x : -q = D * cos Θ) (source_y : h = D * sin Θ) :
    EuclideanGeometry.angle (point r 0) (point 0 h) (point q 0) = Θ - θ := by
  have old : point r 0 - point 0 h = -(d • direction θ) := by
    ext i
    fin_cases i <;> simp [point, direction, PiLp.sub_apply, C.source_y,
      show r = -(d * cos θ) by linarith [C.source_x]]
  have next : point q 0 - point 0 h = -(D • direction Θ) := by
    ext i
    fin_cases i <;> simp [point, direction, PiLp.sub_apply, source_y,
      show q = -(D * cos Θ) by linarith [source_x]]
  change InnerProductGeometry.angle (point r 0 - point 0 h) (point q 0 - point 0 h) = _
  rw [old, next, InnerProductGeometry.angle_neg_neg,
    InnerProductGeometry.angle_smul_left_of_pos _ _ C.radius_pos,
    InnerProductGeometry.angle_smul_right_of_pos _ _ radius]
  exact direction_angle θ Θ
    (sub_nonneg.mpr (C.source_direction_mono order radius angle_pos source_x source_y))
    (by linarith [C.angle_pos])

/-- Rotation, exact addition of the next kite, and separation before addition.
All three regions are explicit sets of points in the same Euclidean plane. -/
theorem rotate_and_move {q D Θ lower upper : ℝ}
    (order : r ≤ q) (radius : 0 < D) (angle_pos : 0 < Θ) (angle_lt_pi : Θ < π)
    (source_x : -q = D * cos Θ) (source_y : h = D * sin Θ)
    (lower_moves : θ ≤ lower) (upper_moves : upper ≤ 2 * π - θ)
    (budget : γ + EuclideanGeometry.angle (point r 0) (point 0 h) (point q 0) ≤ 3 * π / 2) :
    let α := EuclideanGeometry.angle (point r 0) (point 0 h) (point q 0)
    let W : Set Plane := {z | z - point r 0 ∈ polarRegion d γ lower upper}
    let V : Set Plane := {z | z - point r 0 ∈ polarRegion d γ θ (2 * π - θ)}
    let W' : Set Plane := {z | z - point q 0 ∈
      polarRegion D (γ + α) Θ (2 * π - Θ)}
    W ⊆ V ∧ Disjoint V (interior (kite h r q)) ∧ W' = V ∪ kite h r q := by
  rw [C.kite_apex_angle order radius angle_pos angle_lt_pi source_x source_y] at budget ⊢
  have increasing := C.source_direction_mono order radius angle_pos source_x source_y
  have lower_bound : π / 2 ≤ γ + (Θ - θ) := by linarith [C.lower]
  have next := C.moved_coordinates radius angle_pos angle_lt_pi source_x source_y lower_bound budget
  have old_identity : {z | z - point r 0 ∈ polarRegion d γ θ (2 * π - θ)} =
      region h r a b := by
    ext z
    exact (C.mem_region_iff_polar z).symm
  have new_identity : {z | z - point q 0 ∈
      polarRegion D (γ + (Θ - θ)) Θ (2 * π - Θ)} = region h q a b := by
    rw [← region_rescale h q a b (div_pos radius C.radius_pos)]
    ext z
    exact (next.mem_region_iff_polar z).symm
  refine ⟨fun z member => rotate_arms lower_moves upper_moves member, ?_⟩
  change Disjoint _ _ ∧ _ = _
  rw [old_identity, new_identity]
  have step := root_step C.height_pos order C.outward
    (C.next_outward radius angle_pos angle_lt_pi source_x source_y lower_bound budget)
  exact ⟨step.2, step.1⟩

end ArmCoordinates
end SixVertexUnfolding.Wedge
