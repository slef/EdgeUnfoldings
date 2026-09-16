import SixVertexUnfolding.Geometry.VoronoiDiagram

/-! A connected set crossing between nearest-site regions must meet the
actual Voronoi boundary. The proof uses a continuous finite distance minimum. -/

namespace SixVertexUnfolding

open Set

/-- A connected set containing points where two different sites are nearest contains a tie. -/
theorem voronoi_crossing (sources : Set Plane) (finite : sources.Finite)
    (D : Set Plane) (connected : IsPreconnected D) (p q : Plane)
    (hp : p ∈ sources) (hq : q ∈ sources) (different : p ≠ q)
    (x y : Plane) (hx : x ∈ D) (hy : y ∈ D)
    (first : ∀ s ∈ sources, dist p x ≤ dist s x)
    (second : dist q y ≤ dist p y) : (D ∩ voronoiBoundary sources).Nonempty := by
  classical
  let others := finite.toFinset.erase p
  have q_other : q ∈ others := Finset.mem_erase.mpr ⟨different.symm, finite.mem_toFinset.mpr hq⟩
  have nonempty : others.Nonempty := ⟨q, q_other⟩
  let nearest (z : Plane) := others.inf' nonempty (fun s => dist s z)
  have continuous_nearest : Continuous nearest :=
    Continuous.finset_inf'_apply nonempty (fun _ _ => continuous_const.dist continuous_id)
  have at_x : dist p x ≤ nearest x := Finset.le_inf' nonempty _ (fun s hs =>
    first s (finite.mem_toFinset.mp (Finset.mem_erase.mp hs).2))
  have at_y : nearest y ≤ dist p y := (Finset.inf'_le _ q_other).trans second
  obtain ⟨z, hz, equal⟩ := connected.intermediate_value₂ hx hy
    (continuous_const.dist continuous_id).continuousOn continuous_nearest.continuousOn at_x at_y
  obtain ⟨s, hs, attained⟩ := Finset.exists_mem_eq_inf' nonempty (fun s => dist s z)
  refine ⟨z, hz, p, hp, s, finite.mem_toFinset.mp (Finset.mem_erase.mp hs).2,
    (Finset.mem_erase.mp hs).1.symm, equal.trans attained, ?_⟩
  intro t ht
  by_cases same : t = p
  · rw [same]
  · exact equal.le.trans (Finset.inf'_le _ (Finset.mem_erase.mpr ⟨same, finite.mem_toFinset.mpr ht⟩))

end SixVertexUnfolding
