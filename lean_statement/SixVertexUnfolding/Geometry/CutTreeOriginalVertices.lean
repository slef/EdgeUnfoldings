import SixVertexUnfolding.Geometry.CutTreeLeaves
import SixVertexUnfolding.Geometry.CutSetVertexLimits

/-! The original vertices other than the source are genuinely present
among the embedded tree vertices. Its leaves form a subset of this set. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

namespace EmbeddedCutGraph

variable {P : ConvexPolyhedron} {a : frontier P.body} (K : P.EmbeddedCutGraph a)

/-- The source is absent from the embedded cut graph. -/
theorem vertex_ne_source (u : K.vertices) : (u : Space) ≠ (a : Space) := by
  intro same
  have member := K.vertex_in_trace u
  rw [same, P.mem_cutSetInSpace] at member
  exact P.source_not_cutSet a member

/-- An original nonsource vertex cannot be hidden inside a straight graph edge. -/
theorem original_vertex_mem {v : Space} (vertex : v ∈ P.vertices) (different : v ≠ (a : Space)) :
    v ∈ K.vertices := by
  let b : frontier P.body := ⟨v, P.vertex_mem_frontier vertex⟩
  have cut : v ∈ P.cutSetInSpace a := ⟨b, Or.inr ⟨vertex,
    fun same => different (congrArg Subtype.val same)⟩, rfl⟩
  rcases (K.trace v).mp cut with member | ⟨u, w, edge, inside⟩
  · exact member
  · obtain ⟨F, cofacial⟩ := K.cofacial_edges u w edge
    have endpoints := P.vertex_in_segment_is_endpoint vertex
      (F.subset_body (cofacial (left_mem_segment ℝ _ _)))
      (F.subset_body (cofacial (right_mem_segment ℝ _ _)))
      (openSegment_subset_segment ℝ _ _ inside)
    rcases endpoints with same | same
    · exact same ▸ u.property
    · exact same ▸ w.property

/-- Among original vertices, precisely the source is excluded. -/
theorem original_vertex_mem_iff (v : P.Vertex) :
    (v : Space) ∈ K.vertices ↔ (v : Space) ≠ (a : Space) := by
  constructor
  · exact fun member => K.vertex_ne_source ⟨v, member⟩
  · exact K.original_vertex_mem v.property

end EmbeddedCutGraph

namespace SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- The number of cut-tree leaves is bounded by the number of original nonsource vertices. -/
theorem cut_tree_leaf_count (a : frontier P.body) (K : P.EmbeddedCutGraph a) :
    {u : K.vertices | ∃! v, K.graph.Adj u v}.ncard ≤ (P.vertices.erase (a : Space)).card := by
  classical
  let leaves : Set K.vertices := {u | ∃! v, K.graph.Adj u v}
  have included : Subtype.val '' leaves ⊆ (P.vertices.erase (a : Space) : Set Space) := by
    rintro _ ⟨u, ⟨v, edge, only_neighbor⟩, rfl⟩
    exact Finset.mem_erase.mpr ⟨K.vertex_ne_source u,
      graph.cut_graph_leaf_is_vertex small_faces a K u v edge only_neighbor⟩
  have count := ncard_le_ncard included (P.vertices.erase (a : Space)).finite_toSet
  rw [ncard_image_of_injective leaves Subtype.val_injective] at count
  simpa only [ncard_coe_finset] using count

include graph small_faces in
/-- At an original source vertex, there are at most five leaves in the canonical six-vertex models. -/
theorem cut_tree_at_most_five_leaves (a : frontier P.body) (source_vertex : (a : Space) ∈ P.vertices)
    (K : P.EmbeddedCutGraph a) : {u : K.vertices | ∃! v, K.graph.Adj u v}.ncard ≤ 5 := by
  have count := graph.cut_tree_leaf_count small_faces a K
  have size : P.vertices.card = 6 := by
    have size := Fintype.card_congr graph.vertex
    simpa only [P.vertex_card, Fintype.card_fin] using size.symm
  rwa [Finset.card_erase_of_mem source_vertex, size] at count

end SixVertexGraph
end SixVertexUnfolding.ConvexPolyhedron
