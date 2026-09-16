import SixVertexUnfolding.Geometry.CutTreeParameterIncidence
import SixVertexUnfolding.Geometry.CofacialStarCuts
import SixVertexUnfolding.Geometry.JunctionRayMapAgreement

/-! A point on a retained endpoint ray has the same global coordinates
in every triangle that contains it, regardless of edge orientation. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces

theorem global_endpoint_placements_agree {a : frontier P.body} {T : P.CutLocusTree a}
    (charts : CutTreeCharts T)
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val)
    {u v w z : T.vertices} (first : T.graph.Adj u v) (second : T.graph.Adj w z)
    {t : unitInterval} {b : frontier P.body} {x y : Plane} (outside : b ∉ P.starCuts a)
    (first_placement : (charts.global first).PlacesOnRay 0 b x)
    (second_placement : (charts.global second).PlacesOnRay t b y) : x = y := by
  have not_source : b ≠ a := fun same => outside (same ▸ P.source_mem_starCuts a)
  have nonvertex := (charts.global first).endpoint_nonvertex_of_outside_cuts cofacial outside first_placement
  have targets := graph.placed_ray_targets_equal small_faces (charts.global first)
    (charts.global second) not_source first_placement second_placement
  rw [T.closedEdgeTarget_zero] at targets
  rcases T.parameter_endpoint_of_vertex second t targets.symm with rfl | rfl
  · rw [T.closedEdgeTarget_zero] at targets
    have same_vertex : u = w := Subtype.ext (congrArg (fun q : frontier P.body => (q : Space)) targets)
    subst w
    exact graph.global_incident_ray_placements_agree small_faces charts first second nonvertex not_source
      first_placement second_placement
  · rw [T.closedEdgeTarget_one] at targets
    have same_vertex : u = z := Subtype.ext (congrArg (fun q : frontier P.body => (q : Space)) targets)
    subst z
    have reversed := graph.global_ray_placement_reverse small_faces charts second not_source second_placement
    have at_zero : (charts.global second.symm).PlacesOnRay 0 b y := by
      simpa only [unitInterval.symm_one] using reversed
    exact graph.global_incident_ray_placements_agree small_faces charts first second.symm nonvertex not_source
      first_placement at_zero

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
