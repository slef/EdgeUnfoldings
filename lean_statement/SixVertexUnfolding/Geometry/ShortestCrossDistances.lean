import SixVertexUnfolding.Geometry.IntrinsicSurfaceMetric

/-! Distances between two minimizing routes with common endpoints. A common
interior point forces the cross distances needed to rule out local branching. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SurfacePath

open Set

variable {P : ConvexPolyhedron} {a b : Space}

theorem shortest_lengths_equal (first second : P.SurfacePath a b)
    (first_shortest : first.IsShortest) (second_shortest : second.IsShortest) :
    first.length = second.length := le_antisymm (first_shortest second) (second_shortest first)

theorem source_distance (path : P.SurfacePath a b) (shortest : path.IsShortest)
    (finite : path.length ≠ ⊤) (speed : LipschitzWith path.length.toNNReal path.curve)
    (t : unitInterval) : P.surfaceDist a (path.curve t) = path.length.toReal * (t : ℝ) := by
  have elapsed : dist (0 : unitInterval) t = (t : ℝ) := by
    change dist (0 : ℝ) (t : ℝ) = _
    rw [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg t.property.1]
  have equal := path.surfaceDist_along shortest finite speed 0 t
  rwa [path.curve.source, elapsed] at equal

theorem target_distance (path : P.SurfacePath a b) (shortest : path.IsShortest)
    (finite : path.length ≠ ⊤) (speed : LipschitzWith path.length.toNNReal path.curve)
    (t : unitInterval) : P.surfaceDist (path.curve t) b = path.length.toReal * (1 - (t : ℝ)) := by
  have elapsed : dist t (1 : unitInterval) = 1 - (t : ℝ) := by
    change dist (t : ℝ) (1 : ℝ) = _
    rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr t.property.2)]
  have equal := path.surfaceDist_along shortest finite speed t 1
  rwa [path.curve.target, elapsed] at equal

/-- A cross connection cannot save time between equally parametrized shortest routes. -/
theorem cross_distance_lower (first second : P.SurfacePath a b)
    (first_shortest : first.IsShortest) (second_shortest : second.IsShortest)
    (first_finite : first.length ≠ ⊤) (second_finite : second.length ≠ ⊤)
    (first_speed : LipschitzWith first.length.toNNReal first.curve)
    (second_speed : LipschitzWith second.length.toNNReal second.curve)
    (s t : unitInterval) :
    first.length.toReal * ((t : ℝ) - (s : ℝ)) ≤ P.surfaceDist (first.curve s) (second.curve t) := by
  have source_on : a ∈ frontier P.body := first.curve.source ▸ first.on_surface 0
  have target_on : b ∈ frontier P.body := first.curve.target ▸ first.on_surface 1
  have front := first.source_distance first_shortest first_finite first_speed s
  have back := second.target_distance second_shortest second_finite second_speed t
  rw [← first.shortest_lengths_equal second first_shortest second_shortest] at back
  have whole : P.surfaceDist a b = first.length.toReal := by
    rw [surfaceDist, ← first.length_eq_surfaceEDist first_shortest]
  have one := P.surfaceDist_triangle source_on (first.on_surface s) target_on
  have two := P.surfaceDist_triangle (first.on_surface s) (second.on_surface t) target_on
  rw [whole, front] at one
  rw [back] at two
  linarith

/-- Across a common point, the cross connection has exactly the elapsed intrinsic length. -/
theorem cross_distance_eq_of_meet (first second : P.SurfacePath a b)
    (first_shortest : first.IsShortest) (second_shortest : second.IsShortest)
    (first_finite : first.length ≠ ⊤) (second_finite : second.length ≠ ⊤)
    (first_speed : LipschitzWith first.length.toNNReal first.curve)
    (second_speed : LipschitzWith second.length.toNNReal second.curve)
    (s m t : unitInterval) (sm : s ≤ m) (mt : m ≤ t)
    (meet : first.curve m = second.curve m) :
    P.surfaceDist (first.curve s) (second.curve t) = first.length.toReal * ((t : ℝ) - (s : ℝ)) := by
  have elapsed (v w : unitInterval) (vw : v ≤ w) : dist v w = (w : ℝ) - (v : ℝ) := by
    change dist (v : ℝ) (w : ℝ) = _
    rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (show (v : ℝ) ≤ (w : ℝ) from vw))]
  have front := first.surfaceDist_along first_shortest first_finite first_speed s m
  have back := second.surfaceDist_along second_shortest second_finite second_speed m t
  rw [← first.shortest_lengths_equal second first_shortest second_shortest, elapsed m t mt] at back
  rw [elapsed s m sm] at front
  have upper := P.surfaceDist_triangle (first.on_surface s) (first.on_surface m) (second.on_surface t)
  rw [front, meet, back] at upper
  apply le_antisymm _ (first.cross_distance_lower second first_shortest second_shortest
    first_finite second_finite first_speed second_speed s t)
  linarith

end SixVertexUnfolding.ConvexPolyhedron.SurfacePath
