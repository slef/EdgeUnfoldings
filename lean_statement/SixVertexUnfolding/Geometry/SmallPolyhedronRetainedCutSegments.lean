import SixVertexUnfolding.Geometry.RetainedCutSegments
import SixVertexUnfolding.Geometry.SmallPolyhedronStarCutEndpoints

/-! Straight cut-locus segments between retained endpoints stay in
the retained surface: an original extreme vertex cannot lie between
two other points of the convex solid.
This version uses the broader small-polyhedron route results. Where
nonoverlap is needed, it is stated explicitly as separation of the charts. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

variable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include size small_faces

/-- A cut-locus segment with nonvertex endpoints gives a path avoiding all star cuts. -/
theorem small_retained_cut_segment_joined (a b c : frontier P.body)
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val)
    (b_nonvertex : (b : Space) ∉ P.vertices) (c_nonvertex : (c : Space) ∉ P.vertices)
    (on_cut : segment ℝ (b : Space) (c : Space) ⊆ P.cutSetInSpace a) :
    JoinedIn (P.starCuts a)ᶜ b c := by
  let line := Path.segment (b : Space) (c : Space)
  have in_segment (t : unitInterval) : line t ∈ segment ℝ (b : Space) (c : Space) := by
    rw [← Path.range_segment]
    exact mem_range_self t
  have on_surface (t : unitInterval) : line t ∈ frontier P.body :=
    P.cutSetInSpace_subset_boundary a (on_cut (in_segment t))
  let path : Path b c := {
    toFun := fun t => ⟨line t, on_surface t⟩
    continuous_toFun := line.continuous.subtype_mk _
    source' := Subtype.ext line.source
    target' := Subtype.ext line.target }
  refine ⟨path, ?_⟩
  intro t
  apply small_nonvertex_cutPoint_uncut size small_faces a (path t) cofacial
  · exact (P.mem_cutSetInSpace a _).mp (on_cut (in_segment t))
  · intro original
    rcases P.vertex_in_segment_is_endpoint original
      (P.body_closed.frontier_subset b.property) (P.body_closed.frontier_subset c.property)
      (in_segment t) with same | same
    · exact b_nonvertex (same.symm ▸ original)
    · exact c_nonvertex (same.symm ▸ original)

/-- All nonvertex tree vertices are joined in the retained surface. -/
theorem small_retained_cut_vertices_joined {a : frontier P.body} (T : P.CutLocusTree a)
    (charts : CutTreeCharts T)
    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val)
    (u v : T.vertices) (u_nonvertex : (u : Space) ∉ P.vertices) (v_nonvertex : (v : Space) ∉ P.vertices) :
    JoinedIn (P.starCuts a)ᶜ (T.vertexTarget u) (T.vertexTarget v) := by
  let core : Set T.vertices := {w | (w : Space) ∉ P.vertices}
  have lift_walk : ∀ {x y : core}, (T.graph.induce core).Walk x y →
      JoinedIn (P.starCuts a)ᶜ (T.vertexTarget x.val) (T.vertexTarget y.val) := by
    intro x y walk
    induction walk with
    | @nil x =>
      exact JoinedIn.refl (small_nonvertex_cutPoint_uncut size small_faces a (T.vertexTarget x.val) cofacial
        (T.vertexTarget_cut x.val) x.property)
    | @cons x y z first rest ih =>
      exact (small_retained_cut_segment_joined size small_faces a (T.vertexTarget x.val)
        (T.vertexTarget y.val) cofacial x.property y.property
        (T.toEmbeddedCutGraph.closed_edge_in_trace first)).trans ih
  obtain ⟨walk⟩ := T.nonvertex_graph_preconnected charts ⟨u, u_nonvertex⟩ ⟨v, v_nonvertex⟩
  exact lift_walk walk

end SixVertexUnfolding.ConvexPolyhedron
