import SixVertexUnfolding.Geometry.EdgeLocalSourceIdentification
import SixVertexUnfolding.Geometry.EdgeSourceFormulaExtension
import SixVertexUnfolding.Geometry.ShortestExtensionUniqueness

/-! Every actual source at an edge-patch target supplies real nearby
competitors. The shortest proper prefix is unique even if the whole route is not. -/

namespace SixVertexUnfolding.ConvexPolyhedron.EdgeFolding.MetricPatch

open Set

variable {P : ConvexPolyhedron} {center z : Space} {facets : P.NormalizedFacets center}
  {F G : P.Face} {chart : EdgeFolding facets F G} (patch : chart.MetricPatch z)
  (graph : P.SixVertexGraph)
  (small_faces : ∀ H : P.Face, (H.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (H.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- An actual terminal source yields exact-length competitors on both sides of the original edge. -/
theorem terminal_source_competitors (f : P.BoundaryCurve) (geodesic : f ∈ P.geodesicCurves)
    (different : f 0 ≠ f 1) (target : (f 1 : Space) ∈ patch.domain)
    (source : Plane) (terminal : chart.HasTerminalSource f source) :
    ∃ V : Set Space, IsOpen V ∧ (f 1 : Space) ∈ V ∧ ∀ x ∈ V ∩ frontier P.body,
      ∃ path : P.SurfacePath (f 0) x, path.length ≠ ⊤ ∧ path.length.toReal = dist source (chart.unfold x) := by
  let path := P.surfacePathOfCurve f
  obtain ⟨shortest, finite, speed⟩ := P.surfacePathOfCurve_shortest f geodesic
  obtain ⟨m, positive, before, inside, _⟩ := path.common_time_near_target path patch.domain patch.open_domain target
  have distinct_m : f 0 ≠ f m := by
    intro same
    exact positive.ne ((path.shortest_lipschitz_injective
      (fun h => different (Subtype.ext h)) shortest finite speed) (congrArg Subtype.val same))
  have prefix_unique := graph.geodesic_interior_targets_unique small_faces f geodesic different m before
  obtain ⟨other, _, U, openU, fmU, formula⟩ := patch.unique_route_source_distance graph small_faces
    (f 0) (f m) distinct_m inside prefix_unique
  have same := patch.local_formula_identifies_source f geodesic source other terminal target m positive before inside U openU fmU formula
  subst other
  exact patch.source_formula_extension (f 0) (f 1) (f m) target inside source m positive before
    (chart.terminal_formula_extends f geodesic source terminal patch.domain patch.open_domain target patch.metric m before inside)
    U openU fmU formula

end SixVertexUnfolding.ConvexPolyhedron.EdgeFolding.MetricPatch
