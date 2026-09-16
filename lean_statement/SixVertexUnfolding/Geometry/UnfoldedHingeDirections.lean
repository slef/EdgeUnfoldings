import SixVertexUnfolding.Geometry.HingeFirstVariation
import SixVertexUnfolding.Geometry.TriangleMetricComparison

/-! Translate the first-variation equation into straightness in the plane.
Only distances within the two rigid faces and their outward side choice enter. -/

namespace SixVertexUnfolding

/-- Opposite normalized directions place the common endpoint on the straight chord. -/
theorem wbtw_of_normalized_directions_opposite (x z y : Plane) (xz : x ≠ z)
    (opposite : NormedSpace.normalize (x - z) = -NormedSpace.normalize (y - z)) :
    Wbtw ℝ x z y := by
  have unit := NormedSpace.norm_normalize (sub_ne_zero.mpr xz : x - z ≠ 0)
  have difference : (x - z) - (y - z) =
      (‖x - z‖ + ‖y - z‖) • NormedSpace.normalize (x - z) := by
    rw [add_smul, NormedSpace.norm_smul_normalize, opposite, smul_neg,
      NormedSpace.norm_smul_normalize, sub_eq_add_neg]
  have length := congrArg norm difference
  rw [sub_sub_sub_cancel_right, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)), unit, mul_one] at length
  apply dist_add_dist_eq_iff.mp
  simpa only [dist_eq_norm, norm_sub_rev z y] using length.symm

/-- Matching four hinge-to-point distances preserves the hinge component of a difference. -/
theorem hinge_difference_inner_of_distances (p q z x : Space) (P Q Z X : Plane)
    (pq : dist P Q = dist p q) (px : dist P X = dist p x) (qx : dist Q X = dist q x)
    (pz : dist P Z = dist p z) (qz : dist Q Z = dist q z) :
    inner ℝ (Q - P) (X - Z) = inner ℝ (q - p) (x - z) := by
  have first := triangle_inner_of_distances p q x P Q X pq px qx
  have second := triangle_inner_of_distances p q z P Q Z pq pz qz
  have subtract := congrArg₂ (fun a b : ℝ => a - b) first second
  simpa only [← inner_sub_right, sub_sub_sub_cancel_right] using subtract

/-- A hinge point's perpendicular component vanishes; shifting the origin to it changes no side. -/
theorem hinge_remainder_at_line_point (p q z x : Plane)
    (different : p ≠ q) (on_line : z ∈ affineSpan ℝ ({p, q} : Set Plane)) :
    hingeRemainder (NormedSpace.normalize (q - p)) (x - z) = hingeSideVector p q x := by
  have parallel : z - p ∈ Submodule.span ℝ ({q - p} : Set Plane) := by
    have := vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan on_line
      (subset_affineSpan ℝ _ (by simp : p ∈ ({p, q} : Set Plane)))
    simpa only [vectorSpan_pair_rev, vsub_eq_sub] using this
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp parallel
  have unit := NormedSpace.norm_normalize (sub_ne_zero.mpr different.symm : q - p ≠ 0)
  have zero : hingeRemainder (NormedSpace.normalize (q - p)) (z - p) = 0 := by
    have along : r • (q - p) = (r * ‖q - p‖) • NormedSpace.normalize (q - p) := by
      rw [← smul_smul, NormedSpace.norm_smul_normalize]
    rw [← hr, along]
    exact hingeRemainder_smul_axis unit _
  have subtract (u v : Plane) :
      hingeRemainder (NormedSpace.normalize (q - p)) (u - v) =
        hingeRemainder (NormedSpace.normalize (q - p)) u -
        hingeRemainder (NormedSpace.normalize (q - p)) v := by
    simp only [hingeRemainder, inner_sub_right, sub_smul]
    module
  rw [show x - z = (x - p) - (z - p) by abel, subtract, zero, sub_zero]
  rfl

/-- The spatial stationarity equation forces a straight crossing in an outward rigid development. -/
theorem unfolded_stationary_hinge_is_straight (p q z x y : Space) (P Q Z X Y : Plane)
    (hinge_distinct : P ≠ Q) (xz : X ≠ Z) (yz : Y ≠ Z)
    (on_hinge : Z ∈ affineSpan ℝ ({P, Q} : Set Plane))
    (pq : dist P Q = dist p q)
    (px : dist P X = dist p x) (qx : dist Q X = dist q x)
    (py : dist P Y = dist p y) (qy : dist Q Y = dist q y)
    (pz : dist P Z = dist p z) (qz : dist Q Z = dist q z)
    (zx : dist X Z = dist x z) (zy : dist Y Z = dist y z)
    (stationary : inner ℝ (q - p) (x - z) / ‖x - z‖ +
      inner ℝ (q - p) (y - z) / ‖y - z‖ = 0)
    (outward : OppositeHingeSides P Q X Y) : Wbtw ℝ X Z Y := by
  apply wbtw_of_normalized_directions_opposite X Z Y xz
  apply stationary_hinge_directions_opposite (NormedSpace.normalize (Q - P)) _ _
    (NormedSpace.norm_normalize (sub_ne_zero.mpr hinge_distinct.symm))
    (sub_ne_zero.mpr xz) (sub_ne_zero.mpr yz)
  · have x_length : ‖X - Z‖ = ‖x - z‖ := zx
    have y_length : ‖Y - Z‖ = ‖y - z‖ := zy
    simp only [NormedSpace.normalize, real_inner_smul_left,
      hinge_difference_inner_of_distances p q z x P Q Z X pq px qx pz qz,
      hinge_difference_inner_of_distances p q z y P Q Z Y pq py qy pz qz,
      x_length, y_length]
    calc
      _ = ‖Q - P‖⁻¹ * (inner ℝ (q - p) (x - z) / ‖x - z‖ +
        inner ℝ (q - p) (y - z) / ‖y - z‖) := by ring
      _ = 0 := by rw [stationary, mul_zero]
  · rw [hinge_remainder_at_line_point P Q Z X hinge_distinct on_hinge,
      hinge_remainder_at_line_point P Q Z Y hinge_distinct on_hinge]
    exact outward

end SixVertexUnfolding
