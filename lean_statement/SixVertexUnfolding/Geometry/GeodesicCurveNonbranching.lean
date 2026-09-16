import SixVertexUnfolding.Geometry.GeodesicSourceRecovery
import SixVertexUnfolding.Geometry.OctahedralShortestNonbranching

/-! The actual path nonbranching theorem, expressed in the compact space of
boundary-valued curves so that endpoint neighborhoods can be used directly. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
theorem geodesic_curves_agree_of_meeting (f g : P.BoundaryCurve)
    (hf : f ∈ P.geodesicCurves) (hg : g ∈ P.geodesicCurves)
    (different : f 0 ≠ f 1) (source : f 0 = g 0) (target : f 1 = g 1)
    (t : unitInterval) (positive : 0 < t) (before : t < 1) (meet : f t = g t) : f = g := by
  obtain ⟨first_shortest, first_finite, first_speed⟩ := P.surfacePathOfCurve_shortest f hf
  obtain ⟨second_shortest, second_finite, second_speed⟩ := P.surfacePathOfCurve_shortest g hg
  have ha : (f 0 : Space) = (g 0 : Space) := congrArg Subtype.val source
  have hb : (f 1 : Space) = (g 1 : Space) := congrArg Subtype.val target
  let second := (P.surfacePathOfCurve g).cast ha hb
  have same := graph.shortest_routes_agree_of_meeting small_faces (P.surfacePathOfCurve f) second
    (fun h => different (Subtype.ext h)) first_shortest
    ((P.surfacePathOfCurve g).cast_shortest ha hb second_shortest) first_finite second_finite
    first_speed second_speed t positive before (congrArg Subtype.val meet)
  apply BoundedContinuousFunction.ext
  intro u
  exact Subtype.ext (same u)

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
