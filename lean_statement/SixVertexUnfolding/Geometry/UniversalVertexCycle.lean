import SixVertexUnfolding.Geometry.UniversalVertexLink
import SixVertexUnfolding.Geometry.SmallTwoRegularGraph

/-! For six vertices, the actual link of a universal vertex is one
cycle through all five other vertices, rather than a disconnected collection. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- Deleting the source from the vertex type leaves exactly five vertices. -/
theorem six_vertex_link_card (P : ConvexPolyhedron) (size : P.vertices.card = 6)
    (source : P.Vertex) : Nat.card {v : P.Vertex // v ≠ source} = 5 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl (fun v : P.Vertex => v = source),
    Fintype.card_subtype_eq]
  simp [Vertex, size]

/-- The five-vertex link is connected. -/
theorem universal_vertex_link_connected (P : ConvexPolyhedron) (size : P.vertices.card = 6)
    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4)
    (source : P.Vertex) (universal : ∀ v : P.Vertex, v ≠ source → P.edgeGraph.Adj source v) :
    (P.vertexLink source).Connected := by
  classical
  have count : Fintype.card {v : P.Vertex // v ≠ source} = 5 :=
    (Nat.card_eq_fintype_card.symm.trans (P.six_vertex_link_card size source))
  letI : Nonempty {v : P.Vertex // v ≠ source} := Fintype.card_pos_iff.mp (by omega)
  exact small_two_neighbor_graph_connected (P.vertexLink source) (by omega)
    (P.universal_vertex_link_neighbors small_faces source universal)

/-- There is a simple cyclic walk visiting all five other vertices. -/
theorem universal_vertex_link_cycle (P : ConvexPolyhedron) (size : P.vertices.card = 6)
    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4)
    (source : P.Vertex) (universal : ∀ v : P.Vertex, v ≠ source → P.edgeGraph.Adj source v)
    (b : {v : P.Vertex // v ≠ source}) :
    ∃ p : (P.vertexLink source).Walk b b, p.IsCycle ∧ p.toSubgraph.verts = univ := by
  let G := P.vertexLink source
  have connected := P.universal_vertex_link_connected size small_faces source universal
  have cycles : G.IsCycles := by
    intro v _
    obtain ⟨c, d, distinct, neighbors⟩ := P.universal_vertex_link_neighbors small_faces source universal v
    rw [neighbors, Set.ncard_pair distinct]
  obtain ⟨c, d, _, neighbors⟩ := P.universal_vertex_link_neighbors small_faces source universal b
  have neighbor : (G.neighborSet b).Nonempty := by rw [neighbors]; exact ⟨c, Or.inl rfl⟩
  obtain ⟨p, cycle, vertices⟩ := cycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
    (c := G.connectedComponentMk b) (by rfl) neighbor
  refine ⟨p, cycle, vertices.trans ?_⟩
  ext v
  simp only [mem_univ, iff_true]
  exact SimpleGraph.ConnectedComponent.sound (connected v b)

end SixVertexUnfolding.ConvexPolyhedron
