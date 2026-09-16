import SixVertexUnfolding.Geometry.EmbeddedGraphComponents
import SixVertexUnfolding.Geometry.CutSetConnected

/-! The finite embedded graph of the actual cut set is connected. This is
a proved conclusion from the ray retraction, not a graph-data assumption. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

namespace EmbeddedCutGraph

variable {P : ConvexPolyhedron} {a : frontier P.body} (K : P.EmbeddedCutGraph a)

/-- A connected geometric trace makes the finite embedded graph connected. -/
theorem connected_of_trace_connected (connected : IsConnected (P.cutSetInSpace a)) : K.graph.Connected := by
  have nonempty : Nonempty K.vertices := by
    obtain ⟨x, member⟩ := connected.nonempty
    rcases (K.trace x).mp member with vertex | ⟨u, _, _, _⟩
    · exact ⟨⟨x, vertex⟩⟩
    · exact ⟨u⟩
  refine { preconnected := ?_, nonempty := nonempty }
  intro u v
  by_contra unreachable
  let S : Set K.vertices := {w | K.graph.Reachable u w}
  have covers : P.cutSetInSpace a ⊆ K.subtrace S ∪ K.subtrace Sᶜ := by
    intro x member
    rcases (K.trace x).mp member with vertex | ⟨p, q, edge, inside⟩
    · let p : K.vertices := ⟨x, vertex⟩
      by_cases selected : p ∈ S
      · exact Or.inl ((K.mem_subtrace S x).mpr (Or.inl ⟨p, selected, rfl⟩))
      · exact Or.inr ((K.mem_subtrace Sᶜ x).mpr (Or.inl ⟨p, selected, rfl⟩))
    · have on_segment := openSegment_subset_segment ℝ (p : Space) (q : Space) inside
      by_cases selected : p ∈ S
      · exact Or.inl ((K.mem_subtrace S x).mpr (Or.inr ⟨p, selected, q, edge, on_segment⟩))
      · exact Or.inr ((K.mem_subtrace Sᶜ x).mpr (Or.inr ⟨p, selected, q, edge, on_segment⟩))
  have left_nonempty : (P.cutSetInSpace a ∩ K.subtrace S).Nonempty :=
    ⟨u, (K.trace u).mpr (Or.inl u.property),
      (K.mem_subtrace S u).mpr (Or.inl ⟨u, SimpleGraph.Reachable.rfl, rfl⟩)⟩
  have right_nonempty : (P.cutSetInSpace a ∩ K.subtrace Sᶜ).Nonempty :=
    ⟨v, (K.trace v).mpr (Or.inl v.property),
      (K.mem_subtrace Sᶜ v).mpr (Or.inl ⟨v, unreachable, rfl⟩)⟩
  obtain ⟨x, _, hx, hy⟩ := isPreconnected_closed_iff.mp connected.isPreconnected
    (K.subtrace S) (K.subtrace Sᶜ) (K.subtrace_closed S) (K.subtrace_closed Sᶜ)
    covers left_nonempty right_nonempty
  obtain ⟨p, hp, q, hq, reachable⟩ := K.subtrace_intersection hx hy
  exact hq (hp.trans reachable)

end EmbeddedCutGraph

namespace SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- Every exact embedded cut graph in a canonical model is connected. -/
theorem embedded_cut_graph_connected (a : frontier P.body) (K : P.EmbeddedCutGraph a) : K.graph.Connected :=
  K.connected_of_trace_connected (graph.cutSetInSpace_pathConnected small_faces a).isConnected

include graph small_faces in
/-- The actual cut set has a finite connected embedded graph of cofacial edges. -/
theorem exists_connected_cut_graph (a : frontier P.body) :
    ∃ K : P.EmbeddedCutGraph a, K.graph.Connected := by
  obtain ⟨K⟩ := graph.exists_embedded_cut_graph small_faces a
  exact ⟨K, graph.embedded_cut_graph_connected small_faces a K⟩

end SixVertexGraph
end SixVertexUnfolding.ConvexPolyhedron
