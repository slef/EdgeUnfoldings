import SixVertexUnfolding.Geometry.RetainedCutConnectivity
import SixVertexUnfolding.Geometry.SmallPolyhedronRetainedCutSegments
import SixVertexUnfolding.Geometry.SmallPolyhedronRetainedRadialPaths
import SixVertexUnfolding.Geometry.SmallPolyhedronCutTreeCharts

/-! The cut tree with original leaves removed joins every remaining
cut point. Together with the retained radial paths, it joins every
pair of points of the actual uncut surface.
This version uses the broader small-polyhedron route results. Where
nonoverlap is needed, it is stated explicitly as separation of the charts. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

variable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include size small_faces

/-- An interior edge point can join a retained endpoint without reaching an original leaf. -/
theorem small_retained_cut_point_joins_vertex {a : frontier P.body} (T : P.CutLocusTree a)
    (charts : CutTreeCharts T)
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val)
    (b : frontier P.body) (cut : b ∈ P.cutSet a) (nonvertex : (b : Space) ∉ P.vertices) :
    ∃ u : T.vertices, (u : Space) ∉ P.vertices ∧
      JoinedIn (P.starCuts a)ᶜ b (T.vertexTarget u) := by
  have trace : (b : Space) ∈ P.cutSetInSpace a := ⟨b, cut, rfl⟩
  rcases (T.trace b).mp trace with vertex | ⟨u, v, edge, inside⟩
  · exact ⟨⟨b, vertex⟩, nonvertex,
      JoinedIn.refl (small_nonvertex_cutPoint_uncut size small_faces a b cofacial cut nonvertex)⟩
  · have segment_member := openSegment_subset_segment ℝ (u : Space) (v : Space) inside
    have segment_cut := T.toEmbeddedCutGraph.closed_edge_in_trace edge
    rcases T.edge_has_nonvertex_endpoint charts edge with first | last
    · exact ⟨u, first, small_retained_cut_segment_joined size small_faces a b (T.vertexTarget u)
        cofacial nonvertex first
        (((convex_segment (u : Space) (v : Space)).segment_subset segment_member
          (left_mem_segment ℝ _ _)).trans segment_cut)⟩
    · exact ⟨v, last, small_retained_cut_segment_joined size small_faces a b (T.vertexTarget v)
        cofacial nonvertex last
        (((convex_segment (u : Space) (v : Space)).segment_subset segment_member
          (right_mem_segment ℝ _ _)).trans segment_cut)⟩

/-- Every two nonvertex cut points can be joined without crossing a star cut. -/
theorem small_retained_cut_points_joined {a : frontier P.body} (T : P.CutLocusTree a)
    (charts : CutTreeCharts T)
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val)
    (b c : frontier P.body) (b_cut : b ∈ P.cutSet a) (c_cut : c ∈ P.cutSet a)
    (b_nonvertex : (b : Space) ∉ P.vertices) (c_nonvertex : (c : Space) ∉ P.vertices) :
    JoinedIn (P.starCuts a)ᶜ b c := by
  obtain ⟨u, un, to_u⟩ := small_retained_cut_point_joins_vertex size small_faces T charts cofacial b b_cut b_nonvertex
  obtain ⟨v, vn, to_v⟩ := small_retained_cut_point_joins_vertex size small_faces T charts cofacial c c_cut c_nonvertex
  exact (to_u.trans (small_retained_cut_vertices_joined size small_faces T charts cofacial u v un vn)).trans to_v.symm

/-- The actual polyhedral boundary minus the cofacial-source star cuts is path connected. -/
theorem small_cofacial_uncut_surface_pathConnected (a : frontier P.body)
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val) :
    IsPathConnected (P.starCuts a)ᶜ := by
  classical
  obtain ⟨T⟩ := small_exists_regular_cut_tree size small_faces a
  obtain ⟨charts⟩ := small_exists_cut_tree_charts size small_faces a T cofacial
  have nonvertex_exists : ∃ u : T.vertices, (u : Space) ∉ P.vertices := by
    obtain ⟨u⟩ := T.tree.connected.nonempty
    by_cases original : (u : Space) ∈ P.vertices
    · obtain ⟨v, edge, _⟩ := charts.original_leaves u original
      exact ⟨v, (T.edge_has_nonvertex_endpoint charts edge).resolve_left (not_not.mpr original)⟩
    · exact ⟨u, original⟩
  obtain ⟨u, nonvertex⟩ := nonvertex_exists
  apply isPathConnected_iff.mpr
  refine ⟨⟨T.vertexTarget u, small_nonvertex_cutPoint_uncut size small_faces a _ cofacial
    (T.vertexTarget_cut u) nonvertex⟩, ?_⟩
  intro b b_uncut c c_uncut
  obtain ⟨d, dcut, dn, to_d⟩ := small_retained_point_joins_cut_locus size small_faces a cofacial ⟨b, b_uncut⟩
  obtain ⟨e, ecut, en, to_e⟩ := small_retained_point_joins_cut_locus size small_faces a cofacial ⟨c, c_uncut⟩
  exact (to_d.trans (small_retained_cut_points_joined size small_faces T charts cofacial d e dcut ecut dn en)).trans to_e.symm

end SixVertexUnfolding.ConvexPolyhedron
