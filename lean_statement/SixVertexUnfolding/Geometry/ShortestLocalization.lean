import SixVertexUnfolding.Geometry.SurfaceDistance
import SixVertexUnfolding.Geometry.StraightShortestPaths

/-! A short surface route cannot leave a small ambient neighborhood of its
initial point. This lets local developments control globally shortest paths. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SurfacePath

open Set

variable {P : ConvexPolyhedron} {a b : Space}

/-- Every point of a finite route lies within its total length of the initial endpoint. -/
theorem point_dist_le_length (path : P.SurfacePath a b) (finite : path.length ≠ ⊤)
    (t : unitInterval) : dist (path.curve t) a ≤ path.length.toReal := by
  have bound : edist a (path.curve t) ≤ path.length :=
    (le_add_right le_rfl).trans (path.two_chords_le_length t)
  have real_bound := ENNReal.toReal_mono finite bound
  simpa only [edist_dist, ENNReal.toReal_ofReal dist_nonneg, dist_comm a] using real_bound

/-- If the length budget plus the starting offset fits in a ball, the whole route stays in that ball. -/
theorem range_in_ball (path : P.SurfacePath a b) (finite : path.length ≠ ⊤)
    (z : Space) (r : ℝ) (budget : path.length.toReal + dist a z < r) :
    ∀ t, path.curve t ∈ Metric.ball z r := by
  intro t
  change dist (path.curve t) z < r
  linarith [dist_triangle (path.curve t) a z, path.point_dist_le_length finite t]

/-- Any finite comparison route gives a uniform localization bound for every minimizing route. -/
theorem shortest_range_in_ball (path : P.SurfacePath a b) (shortest : path.IsShortest)
    (comparison : P.SurfacePath a b) (comparison_finite : comparison.length ≠ ⊤)
    (z : Space) (r : ℝ) (budget : comparison.length.toReal + dist a z < r) :
    ∀ t, path.curve t ∈ Metric.ball z r := by
  have bound := shortest comparison
  have finite := ne_top_of_le_ne_top comparison_finite bound
  apply path.range_in_ball finite z r
  linarith [ENNReal.toReal_mono comparison_finite bound]

end SixVertexUnfolding.ConvexPolyhedron.SurfacePath
