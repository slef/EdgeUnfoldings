import SixVertexUnfolding.Geometry.EdgeRouteFamilySource
import SixVertexUnfolding.Geometry.SmallPolyhedronEdgeSources
import SixVertexUnfolding.Geometry.SmallPolyhedronFaceSources
import SixVertexUnfolding.Geometry.SmallPolyhedronRouteStability

/-! A connected continuous route family targeting one original edge
has a fixed actual source copy in its joined two-face coordinates.

Here the shortest-route inputs come from the actual vertex fans of a
polyhedron with at most six vertices and triangular/quadrilateral faces.
No canonical graph model is assumed. -/

namespace SixVertexUnfolding.ConvexPolyhedron.EdgeFolding

open Set Filter Topology

variable {P : ConvexPolyhedron} {center : Space} {facets : P.NormalizedFacets center}
  {F G : P.Face} (chart : EdgeFolding facets F G) (size : P.vertices.card ≤ 6)
  (small_faces : ∀ H : P.Face, (H.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (H.val ∩ (P.vertices : Set Space)).ncard = 4)

include size small_faces in
/-- The actual source stays fixed even when routes approach the crease from different incident faces. -/
theorem small_edge_route_family_source (shared : P.ShareEdge F G) (a : frontier P.body)
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X] (x₀ : X)
    (target : X → frontier P.body) (routes : C(X, P.BoundaryCurve))
    (member : ∀ x, routes x ∈ P.geodesicFiber a (target x)) (different : ∀ x, a ≠ target x)
    (on_edge : ∀ x, (target x : Space) ∈ F.val ∩ G.val)
    (nonvertex : ∀ x, (target x : Space) ∉ P.vertices) :
    ∃ source ∈ chart.sourceImages a, ∀ x, chart.HasTerminalSource (routes x) source ∧
      P.surfaceDist a (target x) = dist source (chart.unfold (target x)) := by
  classical
  let patch (x : X) : chart.MetricPatch (target x) :=
    Classical.choice (chart.exists_metric_patch shared (on_edge x) (nonvertex x))
  have first (x : X) : routes x 0 = a := congrArg Prod.fst (member x).2
  have last (x : X) : routes x 1 = target x := congrArg Prod.snd (member x).2
  have sources (x : X) : ∃ source ∈ chart.sourceImages a, chart.HasTerminalSource (routes x) source := by
    simpa only [first x] using chart.small_exists_terminal_source size small_faces (routes x) (member x).1
      (by simpa only [first x, last x] using different x)
      (by simpa only [last x] using (patch x).only_two _ (patch x).center_mem)
  choose source source_mem terminal using sources
  have locally_constant : IsLocallyConstant source := by
    apply (IsLocallyConstant.iff_eventually_eq source).mpr
    intro x
    obtain ⟨p, _, at_x, W, openW, xW, near⟩ := (patch x).small_geodesic_branch_source size small_faces
      (routes x) (member x).1 (by simpa only [first x, last x] using different x)
      (by simpa only [last x] using (patch x).center_mem)
    have same_x := chart.terminal_source_unique (routes x) _ p (terminal x) at_x
    filter_upwards [routes.continuous.continuousAt.eventually (openW.mem_nhds xW)] with y yW
    have actual := (near (routes y) yW (member y).1 ((first y).trans (first x).symm)).1
    exact (chart.terminal_source_unique (routes y) _ p (terminal y) actual).trans same_x.symm
  refine ⟨source x₀, source_mem x₀, ?_⟩
  intro x
  have constant : source x = source x₀ := locally_constant.apply_eq_of_preconnectedSpace x x₀
  have actual : chart.HasTerminalSource (routes x) (source x₀) := constant ▸ terminal x
  refine ⟨actual, ?_⟩
  simpa only [first x, last x] using chart.terminal_source_distance (patch x) (routes x) (member x).1
    (source x₀) actual (by simpa only [last x] using (patch x).center_mem)

end SixVertexUnfolding.ConvexPolyhedron.EdgeFolding
