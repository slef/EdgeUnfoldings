import SixVertexUnfolding.Geometry.CutTreeTargets
import SixVertexUnfolding.Geometry.SegmentFacetIncidence

/-! An open cut-tree edge stays either inside one original face or
inside one original hinge. Facet incidence cannot change in its interior. -/

namespace SixVertexUnfolding.ConvexPolyhedron.CutLocusTree

open Set

variable {P : ConvexPolyhedron} {a : frontier P.body} (T : P.CutLocusTree a)

/-- Any original facet containing one interior edge point contains the whole closed edge. -/
theorem facet_contains_closed_edge {u v : T.vertices} (edge : T.graph.Adj u v)
    (F : P.Face) (t : Ioo (0 : ℝ) 1) (member : (T.openEdgeTarget edge t : Space) ∈ F.val) :
    ∀ s : unitInterval, (T.closedEdgeTarget edge s : Space) ∈ F.val := by
  obtain ⟨H, contains⟩ := T.cofacial_edges u v edge
  have left := H.subset_body (contains (left_mem_segment ℝ (u : Space) (v : Space)))
  have right := H.subset_body (contains (right_mem_segment ℝ (u : Space) (v : Space)))
  have p := T.openEdgeTarget_inside edge t
  have uF := F.isExposed.isExtreme.left_mem_of_mem_openSegment left right member p
  have vF := F.isExposed.isExtreme.right_mem_of_mem_openSegment left right member p
  intro s
  apply F.convex.segment_subset uF vF
  rw [segment_eq_image_lineMap]
  exact ⟨s, s.property, rfl⟩

/-- The incidence alternatives hold along the whole open cut edge, not just near one point. -/
theorem open_edge_facet_type {u v : T.vertices} (edge : T.graph.Adj u v) :
    (∃ F : P.Face, (∀ t : unitInterval, (T.closedEdgeTarget edge t : Space) ∈ F.val) ∧
      ∀ t, ∀ G : P.Face, (T.openEdgeTarget edge t : Space) ∈ G.val → G = F) ∨
    (∃ F G : P.Face, P.ShareEdge F G ∧
      ∀ t : unitInterval, (T.closedEdgeTarget edge t : Space) ∈ F.val ∩ G.val) := by
  let middle : Ioo (0 : ℝ) 1 := ⟨1 / 2, by norm_num⟩
  rcases P.nonvertex_incident_facets (T.openEdgeTarget edge middle).property
    (T.openEdgeTarget_nonvertex edge middle) with ⟨F, member, unique⟩ | ⟨F, G, shared, member, _⟩
  · refine Or.inl ⟨F, T.facet_contains_closed_edge edge F middle member, ?_⟩
    intro t G tG
    exact unique G (T.facet_contains_closed_edge edge G t tG
      ⟨middle, middle.property.1.le, middle.property.2.le⟩)
  · exact Or.inr ⟨F, G, shared, fun t =>
      ⟨T.facet_contains_closed_edge edge F middle member.1 t,
        T.facet_contains_closed_edge edge G middle member.2 t⟩⟩

end SixVertexUnfolding.ConvexPolyhedron.CutLocusTree
