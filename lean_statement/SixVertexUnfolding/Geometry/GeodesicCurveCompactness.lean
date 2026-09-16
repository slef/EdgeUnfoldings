import SixVertexUnfolding.Geometry.IntrinsicSurfaceMetric
import SixVertexUnfolding.Geometry.SurfacePathCompactness

/-! Normalized intrinsic geodesics form a compact family, even while both
endpoints vary. The topology is uniform convergence of actual surface curves. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set Filter BoundedContinuousFunction
open scoped Topology NNReal

/-- Curves with values on the actual boundary, with the uniform metric. -/
abbrev BoundaryCurve (P : ConvexPolyhedron) := unitInterval →ᵇ (frontier P.body)

/-- Intrinsic distances on the compact boundary have one finite common bound. -/
theorem surfaceDist_uniform_bound (P : ConvexPolyhedron) :
    ∃ C : ℝ≥0, ∀ x y : frontier P.body, P.surfaceDist x y ≤ C := by
  letI : CompactSpace (frontier P.body) := isCompact_iff_compactSpace.mp
    (P.body_compact.of_isClosed_subset isClosed_frontier P.body_closed.frontier_subset)
  have bounded : BddAbove (range (fun pair : (frontier P.body) × (frontier P.body) => P.surfaceDist pair.1 pair.2)) :=
    (isCompact_range P.surfaceDist_continuous).bddAbove
  obtain ⟨C, bound⟩ := bounded
  refine ⟨⟨max C 0, le_max_right _ _⟩, ?_⟩
  intro x y
  exact (bound ⟨(x, y), rfl⟩).trans (le_max_left _ _)

/-- The intrinsic constant-speed geodesic equation, with no prescribed endpoints. -/
def geodesicCurves (P : ConvexPolyhedron) : Set P.BoundaryCurve :=
  {f | ∀ s t, P.surfaceDist (f s) (f t) = P.surfaceDist (f 0) (f 1) * dist s t}

/-- The geodesic equation survives uniform limits, since intrinsic distance is continuous. -/
theorem geodesicCurves_closed (P : ConvexPolyhedron) : IsClosed P.geodesicCurves := by
  have evaluation (t : unitInterval) : Continuous (fun f : P.BoundaryCurve => f t) := continuous_eval_const t
  have distance (s t : unitInterval) : Continuous (fun f : P.BoundaryCurve => P.surfaceDist (f s) (f t)) :=
    P.surfaceDist_continuous.comp ((evaluation s).prodMk (evaluation t))
  unfold geodesicCurves
  simp only [setOf_forall]
  exact isClosed_iInter (fun s => isClosed_iInter (fun t =>
    isClosed_eq (distance s t) ((distance 0 1).mul continuous_const)))

/-- Surface curves sharing an ambient speed bound form a compact family. -/
theorem boundary_curves_with_speed_compact (P : ConvexPolyhedron) (C : ℝ≥0) :
    IsCompact {f : P.BoundaryCurve | LipschitzWith C f} := by
  letI : CompactSpace (frontier P.body) := isCompact_iff_compactSpace.mp
    (P.body_compact.of_isClosed_subset isClosed_frontier P.body_closed.frontier_subset)
  have closed : IsClosed {f : P.BoundaryCurve | LipschitzWith C f} :=
    (isClosed_setOf_lipschitzWith C).preimage continuous_coeFun
  apply BoundedContinuousFunction.arzela_ascoli₂ univ isCompact_univ _ closed (fun _ _ _ => mem_univ _)
  apply Metric.equicontinuous_of_continuity_modulus (fun r : ℝ => C * r)
    (by simpa using (tendsto_const_nhds.mul (tendsto_id : Tendsto (id : ℝ → ℝ) (𝓝 0) (𝓝 0))))
  intro x y f
  exact f.property.dist_le_mul x y

/-- All normalized geodesics form a compact family, uniformly over all endpoint pairs. -/
theorem geodesicCurves_compact (P : ConvexPolyhedron) : IsCompact P.geodesicCurves := by
  obtain ⟨C, bound⟩ := P.surfaceDist_uniform_bound
  apply (P.boundary_curves_with_speed_compact C).of_isClosed_subset P.geodesicCurves_closed
  intro f geodesic
  apply LipschitzWith.of_dist_le_mul
  intro s t
  have lower := P.dist_le_surfaceDist (f s).property (f t).property
  rw [geodesic s t] at lower
  exact lower.trans (mul_le_mul_of_nonneg_right (bound (f 0) (f 1)) dist_nonneg)

namespace SurfacePath

variable {P : ConvexPolyhedron} {a b : Space}

/-- Regard a surface path as a curve in the boundary's ordinary subspace topology. -/
noncomputable def boundaryCurve (path : P.SurfacePath a b) : P.BoundaryCurve :=
  mkOfCompact ⟨fun t => ⟨path.curve t, path.on_surface t⟩, path.curve.continuous.subtype_mk _⟩

/-- Every normalized shortest surface route satisfies the compact family's geodesic equation. -/
theorem boundaryCurve_geodesic (path : P.SurfacePath a b) (shortest : path.IsShortest)
    (finite : path.length ≠ ⊤) (speed : LipschitzWith path.length.toNNReal path.curve) :
    path.boundaryCurve ∈ P.geodesicCurves := by
  intro s t
  change P.surfaceDist (path.curve s) (path.curve t) =
    P.surfaceDist (path.curve 0) (path.curve 1) * dist s t
  rw [path.surfaceDist_along shortest finite speed, path.curve.source, path.curve.target,
    surfaceDist, ← path.length_eq_surfaceEDist shortest]

end SurfacePath
end SixVertexUnfolding.ConvexPolyhedron
