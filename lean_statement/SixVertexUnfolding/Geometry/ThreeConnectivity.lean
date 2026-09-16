import SixVertexUnfolding.Geometry.HalfspaceConnectivity
import SixVertexUnfolding.Geometry.DeletionPlane

/-!
Three-connectivity in its literal deletion form. A plane through the removed
vertices and a surviving anchor divides the remaining vertices into two connected
halfspaces. Ascending and descending anchor edges join those parts.
-/

namespace SixVertexUnfolding.ConvexPolyhedron

/-- Orient a nonconstant height so that some original vertex lies above the anchor. -/
theorem orient_plane_toward_vertex (P : ConvexPolyhedron) (deleted : Finset P.Vertex)
    (anchor : P.Vertex) (n : Space) (nonzero : n ≠ 0)
    (flat : ∀ w ∈ deleted, inner ℝ n w = inner ℝ n anchor) :
    ∃ m : Space, (∀ w ∈ deleted, inner ℝ m w = inner ℝ m anchor) ∧
      ∃ w : P.Vertex, inner ℝ m anchor < inner ℝ m w := by
  obtain ⟨w, vertex, different⟩ := P.exists_vertex_height_ne n anchor nonzero
  rcases lt_or_gt_of_ne different with below | above
  · refine ⟨-n, ?_, ⟨w, vertex⟩, ?_⟩
    · intro u hu
      simp only [inner_neg_left, flat u hu]
    · simpa only [inner_neg_left, neg_lt_neg_iff] using below
  · exact ⟨n, flat, ⟨w, vertex⟩, above⟩

/-- Deleting vertices in a plane leaves a connected graph if that plane has a surviving vertex. -/
theorem connected_after_coplanar_deletion (P : ConvexPolyhedron) (deleted : Finset P.Vertex)
    (anchor : {v : P.Vertex | v ∉ deleted}) (n : Space) (nonzero : n ≠ 0)
    (flat : ∀ w ∈ deleted, inner ℝ n w = inner ℝ n anchor.val) :
    (P.edgeGraph.induce {v : P.Vertex | v ∉ deleted}).Connected := by
  let remain := {v : P.Vertex | v ∉ deleted}
  let graph := P.edgeGraph.induce remain
  obtain ⟨height, flat, higher_vertex, above⟩ :=
    P.orient_plane_toward_vertex deleted anchor.val n nonzero flat
  let level := inner ℝ height anchor.val
  have off_plane_survives (w : P.Vertex) (off_plane : inner ℝ height w ≠ level) : w ∈ remain :=
    fun removed => off_plane (flat w removed)
  obtain ⟨up, anchor_up, up_above⟩ := P.exists_ascending_neighbor height anchor.val
    ⟨higher_vertex, above⟩
  let up_in : remain := ⟨up, off_plane_survives up up_above.ne'⟩
  have up_to_anchor : graph.Adj up_in anchor := anchor_up.symm
  have positive_reaches (a : remain) (positive : level < inner ℝ height a.val) :
      graph.Reachable a anchor :=
    (P.halfspace_reachable_avoiding height level deleted (fun w hw => (flat w hw).le)
      a up_in positive up_above).trans up_to_anchor.reachable
  have reaches (a : remain) : graph.Reachable a anchor := by
    rcases lt_trichotomy (inner ℝ height a.val) level with below | equal | above
    · have lower_in_neg : inner ℝ (-height) anchor.val < inner ℝ (-height) a.val := by
        simpa only [inner_neg_left, neg_lt_neg_iff] using below
      obtain ⟨down, anchor_down, down_below⟩ := P.exists_ascending_neighbor (-height) anchor.val
        ⟨a.val, lower_in_neg⟩
      have down_less : inner ℝ height down < level := by
        simpa only [inner_neg_left, neg_lt_neg_iff] using down_below
      let down_in : remain := ⟨down, off_plane_survives down down_less.ne⟩
      have down_to_anchor : graph.Adj down_in anchor := anchor_down.symm
      have removed_below (w : P.Vertex) (hw : w ∈ deleted) :
          inner ℝ (-height) w ≤ inner ℝ (-height) anchor.val := by
        simp only [inner_neg_left, flat w hw, le_refl]
      exact (P.halfspace_reachable_avoiding (-height) (inner ℝ (-height) anchor.val)
        deleted removed_below a down_in lower_in_neg down_below).trans down_to_anchor.reachable
    · have higher : inner ℝ height a.val < inner ℝ height higher_vertex := by
        rw [equal]
        exact above
      obtain ⟨next, edge, increasing⟩ := P.exists_ascending_neighbor height a.val
        ⟨higher_vertex, higher⟩
      have next_above : level < inner ℝ height next := by rwa [equal] at increasing
      let next_in : remain := ⟨next, off_plane_survives next next_above.ne'⟩
      have edge_in : graph.Adj a next_in := edge
      exact edge_in.reachable.trans (positive_reaches next_in next_above)
    · exact positive_reaches a above
  letI : Nonempty remain := ⟨anchor⟩
  exact ⟨fun a b => (reaches a).trans (reaches b).symm⟩

/-- Removing any set of at most two original vertices leaves the original edge graph connected. -/
theorem edgeGraph_three_connected (P : ConvexPolyhedron) (deleted : Finset P.Vertex)
    (small : deleted.card ≤ 2) :
    (P.edgeGraph.induce {v : P.Vertex | v ∉ deleted}).Connected := by
  classical
  have survivor : ∃ v : P.Vertex, v ∉ deleted := by
    by_contra none
    push Not at none
    have all_vertices : deleted = Finset.univ := Finset.eq_univ_of_forall none
    have lower := P.four_le_vertex_count
    have count : Fintype.card P.Vertex = P.vertices.card := by simp [Vertex]
    rw [all_vertices, Finset.card_univ, count] at small
    omega
  obtain ⟨anchor, survives⟩ := survivor
  obtain ⟨normal, nonzero, flat⟩ := P.exists_plane_through_deleted_vertices deleted small anchor
  exact P.connected_after_coplanar_deletion deleted ⟨anchor, survives⟩ normal nonzero flat

end SixVertexUnfolding.ConvexPolyhedron
