import SixVertexUnfolding.Geometry.FlatChartCoordinates
import SixVertexUnfolding.Geometry.MetricSegmentCoordinates
import SixVertexUnfolding.Geometry.IntrinsicSurfaceMetric
import SixVertexUnfolding.Geometry.ShortestLocalDevelopment

/-! Constant-speed shortest routes are affine straight lines in the actual
flat charts. This is a precise local continuation statement, not just a tangent condition. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SurfacePath

open Set

variable {P : ConvexPolyhedron} {a b z : Space}

/-- Intrinsic arc speed becomes ordinary Euclidean speed in a flat chart. -/
theorem coordinate_distance (path : P.SurfacePath a b) (shortest : path.IsShortest)
    (finite : path.length ≠ ⊤) (speed : LipschitzWith path.length.toNNReal path.curve)
    (chart : P.FlatChart z) (s t : unitInterval)
    (hs : path.curve s ∈ chart.map '' chart.domain) (ht : path.curve t ∈ chart.map '' chart.domain) :
    dist (chart.coordinates (path.curve s)) (chart.coordinates (path.curve t)) =
      path.length.toReal * dist s t := by
  rw [chart.coordinates_distance hs ht, path.surfaceDist_along shortest finite speed s t]

/-- A constant-speed shortest portion contained in one flat chart is exactly affine in its parameter. -/
theorem coordinates_eq_lineMap (path : P.SurfacePath a b) (shortest : path.IsShortest)
    (finite : path.length ≠ ⊤) (speed : LipschitzWith path.length.toNNReal path.curve)
    (chart : P.FlatChart z) (s t : unitInterval) (ordered : s < t)
    (contained : ∀ u ∈ Icc s t, path.curve u ∈ chart.map '' chart.domain)
    (u : unitInterval) (hu : u ∈ Icc s t) :
    chart.coordinates (path.curve u) =
      AffineMap.lineMap (chart.coordinates (path.curve s)) (chart.coordinates (path.curve t))
        (((u : ℝ) - (s : ℝ)) / ((t : ℝ) - (s : ℝ))) := by
  have elapsed (v w : unitInterval) (vw : v ≤ w) : dist v w = (w : ℝ) - (v : ℝ) := by
    change dist (v : ℝ) (w : ℝ) = _
    rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (show (v : ℝ) ≤ (w : ℝ) from vw))]
  have hs := contained s ⟨le_rfl, ordered.le⟩
  have ht := contained t ⟨ordered.le, le_rfl⟩
  have middle := contained u hu
  apply point_eq_lineMap_of_distance_ratios _ _ _ (s : ℝ) (u : ℝ) (t : ℝ) path.length.toReal
    ordered hu.1 hu.2
  · rw [path.coordinate_distance shortest finite speed chart s u hs middle, elapsed s u hu.1]
  · rw [path.coordinate_distance shortest finite speed chart u t middle ht, elapsed u t hu.2]
  · rw [path.coordinate_distance shortest finite speed chart s t hs ht, elapsed s t ordered.le]

/-- Every nonvertex interior point of a shortest route has a genuine chart in which the route is affine. -/
theorem exists_local_affine_coordinates (path : P.SurfacePath a b) (shortest : path.IsShortest)
    (finite : path.length ≠ ⊤) (speed : LipschitzWith path.length.toNNReal path.curve)
    (m : unitInterval) (after_start : 0 < m) (before_end : m < 1)
    (not_vertex : path.curve m ∉ P.vertices) :
    ∃ chart : P.FlatChart (path.curve m), ∃ s t : unitInterval, s < m ∧ m < t ∧
      (∀ u ∈ Icc s t, path.curve u ∈ chart.map '' chart.domain) ∧
      ∀ u ∈ Icc s t, chart.coordinates (path.curve u) =
        AffineMap.lineMap (chart.coordinates (path.curve s)) (chart.coordinates (path.curve t))
          (((u : ℝ) - (s : ℝ)) / ((t : ℝ) - (s : ℝ))) := by
  obtain ⟨chart⟩ := P.exists_flat_chart (path.on_surface m) not_vertex
  obtain ⟨U, openU, center, covers⟩ := chart.covers
  obtain ⟨s, t, sm, mt, near⟩ := path.interval_inside_neighborhood m after_start before_end U openU center
  have contained : ∀ u ∈ Icc s t, path.curve u ∈ chart.map '' chart.domain :=
    fun u hu => covers ⟨near u hu, path.on_surface u⟩
  exact ⟨chart, s, t, sm, mt, contained,
    path.coordinates_eq_lineMap shortest finite speed chart s t (sm.trans mt) contained⟩

end SixVertexUnfolding.ConvexPolyhedron.SurfacePath
