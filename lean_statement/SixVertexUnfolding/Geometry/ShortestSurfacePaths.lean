import SixVertexUnfolding.Geometry.SurfacePathCompactness
import SixVertexUnfolding.Geometry.SurfacePathJoining

/-! A shortest route exists between any two points of the polyhedral boundary.
The comparison is with every continuous surface path, without a speed restriction. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set BoundedContinuousFunction
open scoped ENNReal NNReal

/-- Any two boundary points admit a finite shortest surface path. -/
theorem exists_shortest_surface_path (P : ConvexPolyhedron) {a b : Space}
    (ha : a ∈ frontier P.body) (hb : b ∈ frontier P.body) :
    ∃ path : P.SurfacePath a b, path.IsShortest ∧ path.length ≠ ⊤ := by
  obtain ⟨initial, finite⟩ := P.exists_finite_surface_path ha hb
  obtain ⟨fast, speed, _, _⟩ := initial.exists_lipschitz_reparameterization finite
  let C := initial.length.toNNReal
  let first : unitInterval →ᵇ Space := mkOfCompact fast.curve.toContinuousMap
  have first_in : first ∈ P.boundedSpeedCurves a b C :=
    ⟨fast.curve.source, fast.curve.target, fast.on_surface, speed⟩
  obtain ⟨f, hf, minimum⟩ := P.boundedSpeedCurves_minimum a b C ⟨first, first_in⟩
  let path : P.SurfacePath a b := ⟨⟨f.toContinuousMap, hf.1, hf.2.1⟩, hf.2.2.1⟩
  have bounded : path.length ≤ initial.length :=
    (path.length_le_of_lipschitz hf.2.2.2).trans_eq (ENNReal.coe_toNNReal finite)
  refine ⟨path, ?_, ne_top_of_le_ne_top finite bounded⟩
  intro other
  by_cases longer : initial.length ≤ other.length
  · exact bounded.trans longer
  · have shorter : other.length < initial.length := lt_of_not_ge longer
    have finite_other : other.length ≠ ⊤ := ne_top_of_lt shorter
    obtain ⟨replacement, replacement_speed, _, length_bound⟩ :=
      other.exists_lipschitz_reparameterization finite_other
    let g : unitInterval →ᵇ Space := mkOfCompact replacement.curve.toContinuousMap
    have g_in : g ∈ P.boundedSpeedCurves a b C :=
      ⟨replacement.curve.source, replacement.curve.target, replacement.on_surface,
        replacement_speed.weaken ((ENNReal.toNNReal_le_toNNReal finite_other finite).mpr shorter.le)⟩
    have comparison : path.length ≤ replacement.length := by
      rw [path.length_eq_variation, replacement.length_eq_variation]
      exact minimum g g_in
    exact comparison.trans length_bound

/-- A shortest route may be chosen with speed bounded by its own total length. -/
theorem exists_shortest_lipschitz_surface_path (P : ConvexPolyhedron) {a b : Space}
    (ha : a ∈ frontier P.body) (hb : b ∈ frontier P.body) :
    ∃ path : P.SurfacePath a b, path.IsShortest ∧ path.length ≠ ⊤ ∧
      LipschitzWith path.length.toNNReal path.curve := by
  obtain ⟨path, shortest, finite⟩ := P.exists_shortest_surface_path ha hb
  obtain ⟨replacement, speed, _, bound⟩ := path.exists_lipschitz_reparameterization finite
  have equal_length : replacement.length = path.length := le_antisymm bound (shortest replacement)
  refine ⟨replacement, fun other => bound.trans (shortest other), equal_length ▸ finite, ?_⟩
  rwa [equal_length]

end SixVertexUnfolding.ConvexPolyhedron
