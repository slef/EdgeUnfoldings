import SixVertexUnfolding.Geometry.MetricSegmentCoordinates

/-! For sites on a common circle, moving from the center toward one site
makes that site nearest. Only the ordinary triangle inequality is needed. -/

namespace SixVertexUnfolding

open Set

/-- Sampling a site on a smaller concentric circle preserves its nearest-site region. -/
theorem radial_nearest_site (sources : Set Plane) (z : Plane) (R ρ : ℝ)
    (positive : 0 < R) (small_positive : 0 < ρ) (small : ρ ≤ R)
    (common_distance : ∀ p ∈ sources, dist p z = R) (p : Plane) (hp : p ∈ sources) :
    let x := AffineMap.lineMap z p (ρ / R)
    x ∈ Metric.sphere z ρ ∧ ∀ q ∈ sources, dist p x ≤ dist q x := by
  let t := ρ / R
  have t_nonneg : 0 ≤ t := (div_pos small_positive positive).le
  have t_le : t ≤ 1 := (div_le_one positive).mpr small
  have product : t * R = ρ := div_mul_cancel₀ ρ positive.ne'
  have zp : dist z p = R := (dist_comm z p).trans (common_distance p hp)
  have from_center : dist (AffineMap.lineMap z p t) z = ρ := by
    rw [dist_comm, dist_left_lineMap, Real.norm_eq_abs, abs_of_nonneg t_nonneg, zp, product]
  have from_site : dist p (AffineMap.lineMap z p t) = R - ρ := by
    rw [dist_comm, dist_lineMap_right, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr t_le), zp]
    nlinarith
  refine ⟨from_center, ?_⟩
  intro q hq
  have triangle := dist_triangle q (AffineMap.lineMap z p t) z
  rw [common_distance q hq, from_center] at triangle
  change dist p (AffineMap.lineMap z p t) ≤ _
  rw [from_site]
  linarith

end SixVertexUnfolding
