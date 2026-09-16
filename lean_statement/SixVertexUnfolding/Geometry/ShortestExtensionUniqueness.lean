import SixVertexUnfolding.Geometry.UniqueGeodesicPrefixes
import SixVertexUnfolding.Geometry.GeodesicCurveNonbranching

/-! In the canonical models, every proper initial part of any shortest
route is unique, even if the route's final endpoint admits several routes. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set
open scoped ENNReal

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- Any shortest replacement of a proper prefix stays on the original route. -/
theorem shortest_proper_prefix_image (f : P.BoundaryCurve) (geodesic : f ∈ P.geodesicCurves)
    (different : f 0 ≠ f 1) (t : unitInterval) (before : t < 1)
    (front : P.SurfacePath (f 0) (f t)) (front_shortest : front.IsShortest) (front_finite : front.length ≠ ⊤) :
    range front.curve ⊆ range (fun u => (f u : Space)) := by
  let original := P.surfacePathOfCurve f
  obtain ⟨shortest, finite, speed⟩ := P.surfacePathOfCurve_shortest f geodesic
  let tail := original.portion t 1 unitInterval.le_one'
  have tail_finite : tail.length ≠ ⊤ := original.portion_finite finite t 1 _
  let joined := front.join tail
  have joined_finite : joined.length ≠ ⊤ := front.join_finite tail front_finite tail_finite
  have front_length : front.length.toReal = original.length.toReal * (t : ℝ) := by
    rw [front.length_eq_surfaceEDist front_shortest]
    exact original.source_distance shortest finite speed t
  have tail_length : tail.length.toReal = original.length.toReal * (1 - (t : ℝ)) :=
    original.portion_length_constant_speed finite speed t 1 _
  have same_length : joined.length = original.length := by
    apply (ENNReal.toReal_eq_toReal_iff' joined_finite finite).mp
    calc
      joined.length.toReal = (front.length + tail.length).toReal := congrArg ENNReal.toReal (front.join_length tail)
      _ = front.length.toReal + tail.length.toReal := ENNReal.toReal_add front_finite tail_finite
      _ = original.length.toReal := by rw [front_length, tail_length]; ring
  have joined_shortest : joined.IsShortest := fun other => same_length ▸ shortest other
  obtain ⟨normal, normal_shortest, normal_finite, normal_speed, normal_image⟩ :=
    joined.shortest_normalization joined_shortest joined_finite
  obtain ⟨m, after, m_before⟩ := exists_between before
  have m_positive : 0 < m := unitInterval.nonneg'.trans_lt after
  have tail_point : (f m : Space) ∈ range tail.curve := by
    refine ⟨m, ?_⟩
    change (f (min 1 (max t m)) : Space) = (f m : Space)
    rw [max_eq_right after.le, min_eq_right m_before.le]
  have on_normal : (f m : Space) ∈ range normal.curve := by
    rw [normal_image]
    change (f m : Space) ∈ range (front.curve.trans tail.curve)
    rw [Path.trans_range]
    exact Or.inr tail_point
  obtain ⟨r, at_r⟩ := on_normal
  have equal_time : r = m := normal.meeting_parameters_equal original
    (fun h => different (Subtype.ext h)) normal_shortest shortest normal_finite finite normal_speed speed r m at_r
  have meet : f m = normal.boundaryCurve m := by
    apply Subtype.ext
    simpa only [equal_time] using at_r.symm
  have same := graph.geodesic_curves_agree_of_meeting small_faces f normal.boundaryCurve geodesic
    (normal.boundaryCurve_geodesic normal_shortest normal_finite normal_speed) different
    (Subtype.ext normal.curve.source.symm) (Subtype.ext normal.curve.target.symm) m m_positive m_before meet
  have image : range normal.curve = range (fun u => (f u : Space)) := by
    exact congrArg (fun h : P.BoundaryCurve => range (fun u => (h u : Space))) same.symm
  rw [← image, normal_image]
  change range front.curve ⊆ range (front.curve.trans tail.curve)
  rw [Path.trans_range]
  exact subset_union_left

include graph small_faces in
/-- An interior point of any shortest route has a unique shortest route from its source. -/
theorem geodesic_interior_targets_unique (f : P.BoundaryCurve) (geodesic : f ∈ P.geodesicCurves)
    (different : f 0 ≠ f 1) (t : unitInterval) (before : t < 1) :
    (P.geodesicFiber (f 0) (f t)).Subsingleton := by
  have coordinates (g : P.BoundaryCurve) (member : g ∈ P.geodesicFiber (f 0) (f t)) (u : unitInterval) :
      g u = f ⟨(t : ℝ) * (u : ℝ), mul_nonneg t.property.1 u.property.1,
        (mul_le_of_le_one_right t.property.1 u.property.2).trans t.property.2⟩ := by
    obtain ⟨front, shortest, finite, _, same⟩ := P.geodesicFiber_path (f 0) (f t) g member
    apply P.prefix_coordinates_of_image_subset f geodesic different t g member ?_ u
    rintro x ⟨v, rfl⟩
    apply graph.shortest_proper_prefix_image small_faces f geodesic different t before front shortest finite
    exact ⟨v, congrArg (fun h : P.BoundaryCurve => (h v : Space)) same⟩
  intro g hg h hh
  apply BoundedContinuousFunction.ext
  intro u
  exact (coordinates g hg u).trans (coordinates h hh u).symm

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
