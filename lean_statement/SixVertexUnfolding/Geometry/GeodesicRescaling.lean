import SixVertexUnfolding.Geometry.GeodesicFibers
import SixVertexUnfolding.Geometry.ShortestRayEndpoints

/-! Restrict a normalized shortest curve to an initial fraction, keeping
the resulting curve on the unit interval. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set BoundedContinuousFunction

/-- The same curve traversed only up to the prescribed final time. -/
noncomputable def geodesicPrefix (P : ConvexPolyhedron) (f : P.BoundaryCurve)
    (r : unitInterval) : P.BoundaryCurve :=
  mkOfCompact ⟨fun t => f (r * t), f.continuous.comp
    ((continuous_const.mul continuous_subtype_val).subtype_mk _)⟩

theorem geodesicPrefix_apply (P : ConvexPolyhedron) (f : P.BoundaryCurve) (r t : unitInterval) :
    P.geodesicPrefix f r t = f (r * t) := rfl

theorem geodesic_source_distance (P : ConvexPolyhedron) (f : P.BoundaryCurve)
    (geodesic : f ∈ P.geodesicCurves) (t : unitInterval) :
    P.surfaceDist (f 0) (f t) = P.surfaceDist (f 0) (f 1) * (t : ℝ) := by
  rw [geodesic 0 t]
  congr 1
  change dist (0 : ℝ) (t : ℝ) = _
  rw [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg t.property.1]

/-- Every point of a geodesic satisfies the defining shortest-extension equality. -/
theorem geodesic_endpoint_extension (P : ConvexPolyhedron) (f : P.BoundaryCurve)
    (geodesic : f ∈ P.geodesicCurves) (t : unitInterval) :
    f 1 ∈ P.shortestExtensions (f 0) (f t) := by
  have elapsed : dist t (1 : unitInterval) = 1 - (t : ℝ) := by
    change dist (t : ℝ) (1 : ℝ) = _
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr t.property.2)]
    ring
  change P.surfaceDist (f 0) (f 1) = P.surfaceDist (f 0) (f t) + P.surfaceDist (f t) (f 1)
  rw [P.geodesic_source_distance f geodesic t, geodesic t 1, elapsed]
  ring

/-- The intrinsic geodesic equation is preserved by this rescaling. -/
theorem geodesicPrefix_geodesic (P : ConvexPolyhedron) (f : P.BoundaryCurve)
    (geodesic : f ∈ P.geodesicCurves) (r : unitInterval) :
    P.geodesicPrefix f r ∈ P.geodesicCurves := by
  have elapsed (s t : unitInterval) : dist (r * s) (r * t) = (r : ℝ) * dist s t := by
    change dist ((r : ℝ) * (s : ℝ)) ((r : ℝ) * (t : ℝ)) = _
    rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg r.property.1]
    rfl
  have initial : dist (0 : unitInterval) r = (r : ℝ) := by
    change dist (0 : ℝ) (r : ℝ) = _
    rw [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg r.property.1]
  intro s t
  simp only [geodesicPrefix_apply, mul_zero, mul_one]
  rw [geodesic (r * s) (r * t), geodesic 0 r, elapsed, initial]
  ring

end SixVertexUnfolding.ConvexPolyhedron
