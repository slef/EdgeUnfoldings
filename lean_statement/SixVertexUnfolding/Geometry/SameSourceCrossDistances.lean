import SixVertexUnfolding.Geometry.ShortestCrossDistances

/-! Equal-speed shortest routes from one source satisfy the cross-distance
bound even when their final endpoints differ. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SurfacePath

open Set

variable {P : ConvexPolyhedron} {a b c : Space}

/-- The distance from the common source prevents a cross connection from saving time. -/
theorem same_source_cross_distance_lower (first : P.SurfacePath a b) (second : P.SurfacePath a c)
    (first_shortest : first.IsShortest) (second_shortest : second.IsShortest)
    (first_finite : first.length ≠ ⊤) (second_finite : second.length ≠ ⊤)
    (first_speed : LipschitzWith first.length.toNNReal first.curve)
    (second_speed : LipschitzWith second.length.toNNReal second.curve)
    (same_length : first.length = second.length) (s t : unitInterval) :
    first.length.toReal * ((t : ℝ) - (s : ℝ)) ≤ P.surfaceDist (first.curve s) (second.curve t) := by
  have source_on : a ∈ frontier P.body := first.curve.source ▸ first.on_surface 0
  have front := first.source_distance first_shortest first_finite first_speed s
  have back := second.source_distance second_shortest second_finite second_speed t
  rw [← same_length] at back
  have triangle := P.surfaceDist_triangle source_on (first.on_surface s) (second.on_surface t)
  rw [front, back] at triangle
  linarith

/-- Across a common point, two equal-speed rays have the exact elapsed cross distance. -/
theorem same_source_cross_distance_eq (first : P.SurfacePath a b) (second : P.SurfacePath a c)
    (first_shortest : first.IsShortest) (second_shortest : second.IsShortest)
    (first_finite : first.length ≠ ⊤) (second_finite : second.length ≠ ⊤)
    (first_speed : LipschitzWith first.length.toNNReal first.curve)
    (second_speed : LipschitzWith second.length.toNNReal second.curve)
    (same_length : first.length = second.length)
    (s m t : unitInterval) (sm : s ≤ m) (mt : m ≤ t)
    (meet : first.curve m = second.curve m) :
    P.surfaceDist (first.curve s) (second.curve t) = first.length.toReal * ((t : ℝ) - (s : ℝ)) := by
  have elapsed (v w : unitInterval) (vw : v ≤ w) : dist v w = (w : ℝ) - (v : ℝ) := by
    change dist (v : ℝ) (w : ℝ) = _
    rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (show (v : ℝ) ≤ (w : ℝ) from vw))]
  have front := first.surfaceDist_along first_shortest first_finite first_speed s m
  have back := second.surfaceDist_along second_shortest second_finite second_speed m t
  rw [← same_length, elapsed m t mt] at back
  rw [elapsed s m sm] at front
  have upper := P.surfaceDist_triangle (first.on_surface s) (first.on_surface m) (second.on_surface t)
  rw [front, meet, back] at upper
  apply le_antisymm _ (first.same_source_cross_distance_lower second first_shortest second_shortest
    first_finite second_finite first_speed second_speed same_length s t)
  linarith

end SixVertexUnfolding.ConvexPolyhedron.SurfacePath
