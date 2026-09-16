import SixVertexUnfolding.Geometry.Polyhedron

/-! Extreme points of a finite convex hull have strictly exposing linear functionals. -/

namespace SixVertexUnfolding

/-- Strict separation from the hull of the other points exposes a finite-hull extreme point. -/
theorem finite_extreme_strict_support (s : Set Space) (finite_s : s.Finite) {v : Space}
    (extreme : v ∈ (convexHull ℝ s).extremePoints ℝ) :
    ∃ n : Space, ∀ w ∈ s, w ≠ v → inner ℝ n w < inner ℝ n v := by
  have outside : v ∉ convexHull ℝ (s \ {v}) := by
    have excluded := ((convex_convexHull ℝ s).mem_extremePoints_iff_mem_diff_convexHull_diff.mp
      extreme).2
    intro member
    apply excluded
    have inclusion : s \ {v} ⊆ convexHull ℝ s \ {v} :=
      fun _ hw => ⟨subset_convexHull ℝ s hw.1, hw.2⟩
    exact convexHull_mono inclusion member
  obtain ⟨height, level, below, above⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ (s \ {v})) (finite_s.diff.isClosed_convexHull ℝ) outside
  let n := (InnerProductSpace.toDual ℝ Space).symm height
  refine ⟨n, ?_⟩
  intro w hw distinct
  have strict := (below w (subset_convexHull ℝ _ ⟨hw, distinct⟩)).trans above
  simpa only [n, InnerProductSpace.toDual_symm_apply] using strict

namespace ConvexPolyhedron

/-- Every genuine vertex uniquely maximizes some linear height among the original vertices. -/
theorem vertex_strict_support (P : ConvexPolyhedron) {v : Space} (vertex : v ∈ P.vertices) :
    ∃ n : Space, ∀ w ∈ P.vertices, w ≠ v → inner ℝ n w < inner ℝ n v := by
  apply finite_extreme_strict_support (P.vertices : Set Space) P.vertices.finite_toSet
  change v ∈ P.body.extremePoints ℝ
  rwa [P.body_extreme_points]

end ConvexPolyhedron
end SixVertexUnfolding
