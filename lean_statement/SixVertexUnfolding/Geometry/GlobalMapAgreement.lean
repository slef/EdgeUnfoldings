import SixVertexUnfolding.Geometry.GlobalEndpointMapAgreement
import SixVertexUnfolding.Geometry.InteriorRayMapAgreement

/-! All actual radial triangle maps give one coordinate to every
surface point outside the specified straight star cuts. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces

/-- The development is single-valued at every retained surface point. -/
theorem global_triangle_placements_agree {a : frontier P.body} {T : P.CutLocusTree a}
    (charts : CutTreeCharts T)
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val)
    {u v w z : T.vertices} (first : T.graph.Adj u v) (second : T.graph.Adj w z)
    {b : frontier P.body} {x y : Plane} (outside : b ∉ P.starCuts a)
    (first_placement : (charts.global first).Places b x)
    (second_placement : (charts.global second).Places b y) : x = y := by
  have not_source : b ≠ a := fun same => outside (same ▸ P.source_mem_starCuts a)
  obtain ⟨s, first_ray⟩ := ((charts.global first).places_iff_ray b x).mp first_placement
  obtain ⟨t, second_ray⟩ := ((charts.global second).places_iff_ray b y).mp second_placement
  by_cases zero : s = 0
  · subst s
    exact graph.global_endpoint_placements_agree small_faces charts cofacial first second outside first_ray second_ray
  by_cases one : s = 1
  · subst s
    have reversed := graph.global_ray_placement_reverse small_faces charts first not_source first_ray
    have at_zero : (charts.global first.symm).PlacesOnRay 0 b x := by
      simpa only [unitInterval.symm_one] using reversed
    exact graph.global_endpoint_placements_agree small_faces charts cofacial first.symm second outside at_zero second_ray
  have positive : 0 < s := lt_of_le_of_ne s.property.1 (Ne.symm zero)
  have before : s < 1 := lt_of_le_of_ne s.property.2 one
  have targets := graph.placed_ray_targets_equal small_faces (charts.global first)
    (charts.global second) not_source first_ray second_ray
  have same_edge := T.same_edge_of_interior_target first second positive before targets
  rcases Sym2.eq_iff.mp same_edge with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have same_parameter : s = t := T.closedEdgeTarget_injective first targets
    subst t
    exact graph.interior_ray_placements_agree small_faces (charts.global first) positive before not_source first_ray second_ray
  · have reversed := graph.global_ray_placement_reverse small_faces charts second not_source second_ray
    have same_target := graph.placed_ray_targets_equal small_faces (charts.global first)
      (charts.global second.symm) not_source first_ray reversed
    have same_parameter : s = unitInterval.symm t := T.closedEdgeTarget_injective first same_target
    rw [← same_parameter] at reversed
    exact graph.interior_ray_placements_agree small_faces (charts.global first) positive before not_source first_ray reversed

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
