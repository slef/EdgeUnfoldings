import SixVertexUnfolding.Geometry.VertexNeighborLink
import SixVertexUnfolding.Geometry.SpanningCycleOrder

/-! Order the actual edge neighbors and incident faces around any vertex
of a small polyhedron. No canonical global vertex labels are used. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

variable (P : ConvexPolyhedron) (size : P.vertices.card ≤ 6)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)
  (pole : P.Vertex) {n : ℕ} [NeZero n] (degree : P.edgeGraph.degree pole = n)

include size small_faces degree in
/-- Consecutive original edge neighbors share an original face at the pole. -/
theorem neighborLink_cyclic_order :
    ∃ order : Fin n ≃ P.edgeGraph.neighborSet pole,
      ∀ i : Fin n, (P.neighborLink pole).Adj (order i) (order (i + 1)) := by
  classical
  let G := P.neighborLink pole
  have connected := P.neighborLink_connected small_faces size pole
  have cycles : G.IsCycles := by
    intro v _
    obtain ⟨c, d, different, neighbors⟩ := P.neighborLink_two_neighbors small_faces pole v
    rw [neighbors, Set.ncard_pair different]
  have count : Fintype.card (P.edgeGraph.neighborSet pole) = n :=
    (SimpleGraph.card_neighborSet_eq_degree _ _).trans degree
  obtain ⟨b⟩ := Fintype.card_pos_iff.mp (show 0 < Fintype.card (P.edgeGraph.neighborSet pole) by
    rw [count]; exact NeZero.pos n)
  obtain ⟨c, d, _, neighbors⟩ := P.neighborLink_two_neighbors small_faces pole b
  have nonempty : (G.neighborSet b).Nonempty := by rw [neighbors]; exact ⟨c, Or.inl rfl⟩
  obtain ⟨p, cycle, vertices⟩ := cycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
    (c := G.connectedComponentMk b) (by rfl) nonempty
  have covers : p.toSubgraph.verts = univ := by
    rw [vertices]
    ext v
    simp only [mem_univ, iff_true]
    exact SimpleGraph.ConnectedComponent.sound (connected v b)
  exact spanning_cycle_order G count p cycle covers

include size small_faces degree in
/-- Every consecutive neighbor pair has its actual supporting face. -/
theorem exists_neighbor_face_order :
    ∃ order : Fin n ≃ P.edgeGraph.neighborSet pole, ∃ faces : Fin n → P.Face,
      ∀ i : Fin n, (pole : Space) ∈ (faces i).val ∧
        ((order i).val : Space) ∈ (faces i).val ∧
        ((order (i + 1)).val : Space) ∈ (faces i).val := by
  obtain ⟨order, consecutive⟩ := P.neighborLink_cyclic_order size small_faces pole degree
  choose faces on_face using fun i => (consecutive i).2
  exact ⟨order, faces, on_face⟩

end SixVertexUnfolding.ConvexPolyhedron
