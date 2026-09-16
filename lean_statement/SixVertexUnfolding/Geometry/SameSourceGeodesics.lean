import SixVertexUnfolding.Geometry.SameSourceNonbranching
import SixVertexUnfolding.Geometry.OctahedralShortestNonbranching
import SixVertexUnfolding.Geometry.GeodesicCurvePaths

/-! Equal-speed geodesics from the same source cannot meet and then branch,
even if their final endpoints are initially allowed to differ. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- Interior meeting identifies the entire two equal-length rays, including their endpoints. -/
theorem same_source_geodesics_agree (f g : P.BoundaryCurve)
    (hf : f ∈ P.geodesicCurves) (hg : g ∈ P.geodesicCurves)
    (different : f 0 ≠ f 1) (source : f 0 = g 0)
    (same_length : P.surfaceDist (f 0) (f 1) = P.surfaceDist (g 0) (g 1))
    (t : unitInterval) (positive : 0 < t) (before : t < 1) (meet : f t = g t) : f = g := by
  let first := P.surfacePathOfCurve f
  let second := (P.surfacePathOfCurve g).cast (congrArg Subtype.val source) rfl
  obtain ⟨first_shortest, first_finite, first_speed⟩ := P.surfacePathOfCurve_shortest f hf
  obtain ⟨second_shortest, second_finite, second_speed⟩ := P.surfacePathOfCurve_shortest g hg
  have lengths : first.length = second.length := by
    apply (ENNReal.toReal_eq_toReal_iff' first_finite second_finite).mp
    rw [first.length_eq_surfaceEDist first_shortest]
    change P.surfaceDist (f 0) (f 1) = (P.surfacePathOfCurve g).length.toReal
    rw [(P.surfacePathOfCurve g).length_eq_surfaceEDist second_shortest]
    exact same_length
  have equal := first.same_source_agree_of_meeting second first_shortest
    ((P.surfacePathOfCurve g).cast_shortest (congrArg Subtype.val source) rfl second_shortest)
    first_finite second_finite first_speed second_speed lengths
    (graph.shortest_lipschitz_avoids_vertices small_faces first
      (fun same => different (Subtype.ext same)) first_shortest first_finite first_speed)
    t positive before (congrArg Subtype.val meet)
  apply BoundedContinuousFunction.ext
  intro u
  exact Subtype.ext (equal u)

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
