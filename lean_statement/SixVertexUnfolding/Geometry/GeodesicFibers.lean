import SixVertexUnfolding.Geometry.GeodesicEndpointStability
import SixVertexUnfolding.Geometry.FinitelyManyShortestRoutes

/-! For prescribed endpoints, the compact family consists of exactly the
actual normalized shortest paths. In the canonical models its fibers are finite. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set BoundedContinuousFunction

/-- All normalized shortest curves with these prescribed boundary endpoints. -/
def geodesicFiber (P : ConvexPolyhedron) (a b : frontier P.body) : Set P.BoundaryCurve :=
  {f | f ∈ P.geodesicCurves ∧ P.curveEndpoints f = (a, b)}

theorem geodesicFiber_compact (P : ConvexPolyhedron) (a b : frontier P.body) :
    IsCompact (P.geodesicFiber a b) :=
  P.geodesicCurves_compact.inter_right (isClosed_eq P.curveEndpoints_continuous continuous_const)

/-- Every member of the fiber is the boundary curve of a genuine optimal surface path. -/
theorem geodesicFiber_path (P : ConvexPolyhedron) (a b : frontier P.body)
    (f : P.BoundaryCurve) (member : f ∈ P.geodesicFiber a b) :
    ∃ path : P.SurfacePath a b, path.IsShortest ∧ path.length ≠ ⊤ ∧
      LipschitzWith path.length.toNNReal path.curve ∧ path.boundaryCurve = f := by
  have first : (a : Space) = (f 0 : Space) := congrArg Subtype.val (congrArg Prod.fst member.2).symm
  have last : (b : Space) = (f 1 : Space) := congrArg Subtype.val (congrArg Prod.snd member.2).symm
  obtain ⟨shortest, finite, speed⟩ := P.surfacePathOfCurve_shortest f member.1
  refine ⟨(P.surfacePathOfCurve f).cast first last, ?_, finite, speed, ?_⟩
  · exact SurfacePath.cast_shortest _ first last shortest
  · exact P.surfacePathOfCurve_boundaryCurve f

theorem geodesicFiber_nonempty (P : ConvexPolyhedron) (a b : frontier P.body) :
    (P.geodesicFiber a b).Nonempty := by
  obtain ⟨path, shortest, finite, speed⟩ := P.exists_shortest_lipschitz_surface_path a.property b.property
  refine ⟨path.boundaryCurve, path.boundaryCurve_geodesic shortest finite speed, ?_⟩
  apply Prod.ext <;> apply Subtype.ext
  · exact path.curve.source
  · exact path.curve.target

namespace SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- Distinct endpoints in a canonical model have a finite, nonempty compact geodesic fiber. -/
theorem geodesicFiber_finite (a b : frontier P.body) (different : a ≠ b) :
    (P.geodesicFiber a b).Finite := by
  have paths := graph.finite_shortest_routes small_faces a b (fun h => different (Subtype.ext h))
  apply (paths.image SurfacePath.boundaryCurve).subset
  intro f hf
  obtain ⟨path, shortest, finite, speed, same⟩ := P.geodesicFiber_path a b f hf
  exact ⟨path, ⟨shortest, finite, speed⟩, same⟩

end SixVertexGraph
end SixVertexUnfolding.ConvexPolyhedron
