import SixVertexUnfolding.Geometry.PlanarCircleTopology
import SixVertexUnfolding.Geometry.VoronoiCrossing
import SixVertexUnfolding.Geometry.RadialNearestSites

/-! Three or more sites on a common circle force at least two distinct
Voronoi branches on every smaller concentric circle. -/

namespace SixVertexUnfolding

open Set

/-- A multiple-site Voronoi junction cannot meet a surrounding circle in at most one point. -/
theorem voronoi_circle_not_subsingleton (sources : Set Plane) (finite : sources.Finite)
    (z : Plane) (R ρ : ℝ) (positive : 0 < R) (small_positive : 0 < ρ) (small : ρ ≤ R)
    (common_distance : ∀ p ∈ sources, dist p z = R) (many : 2 < sources.ncard) :
    ¬ (Metric.sphere z ρ ∩ voronoiBoundary sources).Subsingleton := by
  intro unique
  let sample (p : Plane) := AffineMap.lineMap z p (ρ / R)
  have sample_injective : Function.Injective sample := fun p q same =>
    lineMap_right_unique z p q (ρ / R) (div_pos small_positive positive).ne' same
  have sampled (p : Plane) (hp : p ∈ sources) : sample p ∈ Metric.sphere z ρ ∧
      ∀ q ∈ sources, dist p (sample p) ≤ dist q (sample p) :=
    radial_nearest_site sources z R ρ positive small_positive small common_distance p hp
  obtain ⟨p, hp, q, hq, r, hr, pq, pr, qr⟩ := (two_lt_ncard finite).mp many
  have connected : IsPreconnected (Metric.sphere z ρ) :=
    isPreconnected_sphere (by rw [← Module.finrank_eq_rank]; simp [Plane]) z ρ
  obtain ⟨w, w_circle, w_cut⟩ := voronoi_crossing sources finite _ connected p q hp hq pq
    (sample p) (sample q) (sampled p hp).1 (sampled q hq).1
    (sampled p hp).2 ((sampled q hq).2 p hp)
  let D := Metric.sphere z ρ \ {w}
  have connected_D : IsPreconnected D := punctured_planar_circle_preconnected z ρ small_positive ⟨w, w_circle⟩
  have impossible (s t : Plane) (hs : s ∈ sources) (ht : t ∈ sources) (different : s ≠ t)
      (sw : sample s ≠ w) (tw : sample t ≠ w) : False := by
    obtain ⟨x, hx, tie⟩ := voronoi_crossing sources finite D connected_D s t hs ht different
      (sample s) (sample t) ⟨(sampled s hs).1, sw⟩ ⟨(sampled t ht).1, tw⟩
      (sampled s hs).2 ((sampled t ht).2 s hs)
    exact hx.2 (unique ⟨hx.1, tie⟩ ⟨w_circle, w_cut⟩)
  by_cases pw : sample p = w
  · exact impossible q r hq hr qr
      (fun same => pq (sample_injective (pw.trans same.symm)))
      (fun same => pr (sample_injective (pw.trans same.symm)))
  · by_cases qw : sample q = w
    · exact impossible p r hp hr pr pw
        (fun same => qr (sample_injective (qw.trans same.symm)))
    · exact impossible p q hp hq pq pw qw

end SixVertexUnfolding
