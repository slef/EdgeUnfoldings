import SixVertexUnfolding.Geometry.SurfaceDistanceTopology
import SixVertexUnfolding.Geometry.ShortestSimplePaths

/-! The boundary with shortest-path distance is a compact geodesic metric
space, with exactly its existing Euclidean subspace topology. This metric is
an explicit internal construction, not a replacement of the public definitions. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set Filter
open scoped Topology ENNReal NNReal

/-- Intrinsic balls give the same open sets as the actual boundary topology. -/
theorem surfaceDist_open_iff (P : ConvexPolyhedron) (U : Set (frontier P.body)) :
    IsOpen U ↔ ∀ x ∈ U, ∃ ε > 0, ∀ y : frontier P.body, P.surfaceDist x y < ε → y ∈ U := by
  constructor
  · intro openU x hx
    obtain ⟨ε, positive, contained⟩ := Metric.isOpen_iff.mp openU x hx
    refine ⟨ε, positive, fun y hy => contained ?_⟩
    change dist (y : Space) (x : Space) < ε
    rw [dist_comm]
    exact (P.dist_le_surfaceDist x.property y.property).trans_lt hy
  · intro balls
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    obtain ⟨ε, positive, contained⟩ := balls x hx
    have continuous : Continuous (fun y : frontier P.body => P.surfaceDist x y) :=
      (P.surfaceDist_continuousOn x.property).restrict
    have near : ∀ᶠ y : frontier P.body in 𝓝 x, P.surfaceDist x y < ε :=
      continuous.continuousAt.eventually_lt_const (show P.surfaceDist x x < ε by
        rw [P.surfaceDist_self x.property]; exact positive)
    exact mem_of_superset near contained

/-- Intrinsic distance defines a metric while preserving the existing boundary topology. -/
@[reducible] noncomputable def surfaceMetric (P : ConvexPolyhedron) : MetricSpace (frontier P.body) :=
  MetricSpace.ofDistTopology (fun x y => P.surfaceDist x y)
    (fun x => P.surfaceDist_self x.property)
    (fun x y => P.surfaceDist_comm x y)
    (fun x y z => P.surfaceDist_triangle x.property y.property z.property)
    P.surfaceDist_open_iff
    (fun x y zero => Subtype.ext ((P.surfaceDist_eq_zero_iff x.property y.property).mp zero))

/-- The intrinsic surface remains compact; compactness is not asserted for a new, unverified topology. -/
theorem surfaceMetric_compact (P : ConvexPolyhedron) :
    letI := P.surfaceMetric
    CompactSpace (frontier P.body) := by
  exact isCompact_iff_compactSpace.mp
    (P.body_compact.of_isClosed_subset isClosed_frontier P.body_compact.isClosed.frontier_subset)

/-- Along a shortest route parametrized at constant arc speed, intrinsic distance equals elapsed arc length. -/
theorem SurfacePath.surfaceDist_along {P : ConvexPolyhedron} {a b : Space}
    (path : P.SurfacePath a b) (shortest : path.IsShortest) (finite : path.length ≠ ⊤)
    (speed : LipschitzWith path.length.toNNReal path.curve) (s t : unitInterval) :
    P.surfaceDist (path.curve s) (path.curve t) = path.length.toReal * dist s t := by
  wlog ordered : s ≤ t generalizing s t
  · rw [P.surfaceDist_comm, dist_comm s t]
    exact this t s (le_of_not_ge ordered)
  have length := (path.portion s t ordered).length_eq_surfaceEDist
    (path.portion_shortest shortest finite s t ordered)
  rw [surfaceDist, ← length, path.portion_length_constant_speed finite speed s t ordered]
  congr 1
  change (t : ℝ) - (s : ℝ) = dist (s : ℝ) (t : ℝ)
  rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (show (s : ℝ) ≤ (t : ℝ) from ordered))]

/-- Every pair of intrinsic surface points is joined by a metric geodesic on the unit interval. -/
theorem surfaceMetric_geodesic (P : ConvexPolyhedron) (a b : frontier P.body) :
    ∃ route : Path a b, ∀ s t : unitInterval,
      P.surfaceDist (route s) (route t) = P.surfaceDist a b * dist s t := by
  obtain ⟨path, shortest, finite, speed⟩ := P.exists_shortest_lipschitz_surface_path a.property b.property
  let route : Path a b := {
    toFun := fun t => ⟨path.curve t, path.on_surface t⟩
    continuous_toFun := path.curve.continuous.subtype_mk _
    source' := Subtype.ext path.curve.source
    target' := Subtype.ext path.curve.target }
  refine ⟨route, fun s t => ?_⟩
  change P.surfaceDist (path.curve s) (path.curve t) = P.surfaceDist a b * dist s t
  rw [path.surfaceDist_along shortest finite speed s t, surfaceDist, ← path.length_eq_surfaceEDist shortest]

end SixVertexUnfolding.ConvexPolyhedron
