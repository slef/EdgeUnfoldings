import SixVertexUnfolding.Geometry.UniqueShortestImages
import SixVertexUnfolding.Geometry.ShortestCrossDistances

/-! Every prefix of a unique shortest route is unique. The argument compares
all continuous surface paths; it does not assume any cut-locus theorem. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set
open scoped ENNReal

/-- Replacing a prefix by any shortest route leaves an optimal whole route, hence the same whole image. -/
theorem shortest_prefix_image_subset (P : ConvexPolyhedron) (f : P.BoundaryCurve)
    (geodesic : f ∈ P.geodesicCurves) (unique : (P.geodesicFiber (f 0) (f 1)).Subsingleton)
    (t : unitInterval) (front : P.SurfacePath (f 0) (f t))
    (prefix_shortest : front.IsShortest) (prefix_finite : front.length ≠ ⊤) :
    range front.curve ⊆ range (fun u => (f u : Space)) := by
  let original := P.surfacePathOfCurve f
  obtain ⟨shortest, finite, speed⟩ := P.surfacePathOfCurve_shortest f geodesic
  let tail := original.portion t 1 unitInterval.le_one'
  have tail_finite : tail.length ≠ ⊤ := original.portion_finite finite t 1 _
  let joined := front.join tail
  have joined_finite : joined.length ≠ ⊤ := front.join_finite tail prefix_finite tail_finite
  have prefix_length : front.length.toReal = original.length.toReal * (t : ℝ) := by
    rw [front.length_eq_surfaceEDist prefix_shortest]
    exact original.source_distance shortest finite speed t
  have tail_length : tail.length.toReal = original.length.toReal * (1 - (t : ℝ)) :=
    original.portion_length_constant_speed finite speed t 1 _
  have same_length : joined.length = original.length := by
    apply (ENNReal.toReal_eq_toReal_iff' joined_finite finite).mp
    calc
      joined.length.toReal = (front.length + tail.length).toReal := congrArg ENNReal.toReal (front.join_length tail)
      _ = front.length.toReal + tail.length.toReal := ENNReal.toReal_add prefix_finite tail_finite
      _ = original.length.toReal := by rw [prefix_length, tail_length]; ring
  have joined_shortest : joined.IsShortest := fun other => same_length ▸ shortest other
  have image := P.unique_shortest_image f geodesic unique joined joined_shortest joined_finite
  rw [← image]
  change range front.curve ⊆ range (front.curve.trans tail.curve)
  rw [Path.trans_range]
  exact subset_union_left

/-- A shortest route contained in a longer geodesic's image has the exact prefix parametrization. -/
theorem prefix_coordinates_of_image_subset (P : ConvexPolyhedron) (f : P.BoundaryCurve)
    (geodesic : f ∈ P.geodesicCurves)
    (different : f 0 ≠ f 1) (t : unitInterval) (g : P.BoundaryCurve)
    (member : g ∈ P.geodesicFiber (f 0) (f t))
    (contains : range (fun u => (g u : Space)) ⊆ range (fun u => (f u : Space))) (u : unitInterval) :
    g u = f ⟨(t : ℝ) * (u : ℝ), mul_nonneg t.property.1 u.property.1,
      (mul_le_of_le_one_right t.property.1 u.property.2).trans t.property.2⟩ := by
  let original := P.surfacePathOfCurve f
  obtain ⟨shortest, finite, speed⟩ := P.surfacePathOfCurve_shortest f geodesic
  obtain ⟨front, prefix_shortest, prefix_finite, prefix_speed, prefix_eq⟩ :=
    P.geodesicFiber_path (f 0) (f t) g member
  have point : (g u : Space) ∈ range (fun v => (f v : Space)) := contains ⟨u, rfl⟩
  obtain ⟨r, at_r⟩ := point
  change (f r : Space) = (g u : Space) at at_r
  have length_positive : 0 < original.length.toReal :=
    original.length_toReal_pos (fun h => different (Subtype.ext h)) finite
  have prefix_length : front.length.toReal = original.length.toReal * (t : ℝ) := by
    rw [front.length_eq_surfaceEDist prefix_shortest]
    exact original.source_distance shortest finite speed t
  have first := original.source_distance shortest finite speed r
  have second := front.source_distance prefix_shortest prefix_finite prefix_speed u
  have at_u : front.curve u = (g u : Space) := congrArg (fun h : P.BoundaryCurve => (h u : Space)) prefix_eq
  change P.surfaceDist (f 0) (f r) = original.length.toReal * (r : ℝ) at first
  rw [at_r] at first
  rw [at_u, prefix_length] at second
  have time : (r : ℝ) = (t : ℝ) * (u : ℝ) := by nlinarith
  apply Subtype.ext
  exact at_r.symm.trans (congrArg (fun v : unitInterval => (f v : Space)) (Subtype.ext time))

/-- A normalized shortest route to an intermediate point follows exactly the corresponding prefix. -/
theorem unique_prefix_coordinates (P : ConvexPolyhedron) (f : P.BoundaryCurve)
    (geodesic : f ∈ P.geodesicCurves) (unique : (P.geodesicFiber (f 0) (f 1)).Subsingleton)
    (different : f 0 ≠ f 1) (t : unitInterval) (g : P.BoundaryCurve)
    (member : g ∈ P.geodesicFiber (f 0) (f t)) (u : unitInterval) :
    g u = f ⟨(t : ℝ) * (u : ℝ), mul_nonneg t.property.1 u.property.1,
      (mul_le_of_le_one_right t.property.1 u.property.2).trans t.property.2⟩ := by
  obtain ⟨front, shortest, finite, _, same⟩ := P.geodesicFiber_path (f 0) (f t) g member
  apply P.prefix_coordinates_of_image_subset f geodesic different t g member ?_ u
  rintro x ⟨v, rfl⟩
  apply P.shortest_prefix_image_subset f geodesic unique t front shortest finite
  exact ⟨v, congrArg (fun h : P.BoundaryCurve => (h v : Space)) same⟩

/-- Every intermediate target on a unique route has a unique shortest route from the same source. -/
theorem unique_geodesic_prefixes (P : ConvexPolyhedron) (f : P.BoundaryCurve)
    (geodesic : f ∈ P.geodesicCurves) (unique : (P.geodesicFiber (f 0) (f 1)).Subsingleton)
    (different : f 0 ≠ f 1) (t : unitInterval) : (P.geodesicFiber (f 0) (f t)).Subsingleton := by
  intro g hg h hh
  apply BoundedContinuousFunction.ext
  intro u
  exact (P.unique_prefix_coordinates f geodesic unique different t g hg u).trans
    (P.unique_prefix_coordinates f geodesic unique different t h hh u).symm

end SixVertexUnfolding.ConvexPolyhedron
