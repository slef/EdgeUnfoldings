import SixVertexUnfolding.Geometry.FacetCornerNeighbors
import SixVertexUnfolding.Geometry.EdgeFacePairs
import SixVertexUnfolding.Geometry.VertexFigureEdges
import SixVertexUnfolding.Geometry.SmallTwoRegularGraph

/-! The local face cycle on the actual edge neighbors of any vertex.
Quadrilateral diagonals are excluded by using original edge neighbors. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

def neighborLink (P : ConvexPolyhedron) (pole : P.Vertex) :
    SimpleGraph (P.edgeGraph.neighborSet pole) where
  Adj u v := u ≠ v ∧ ∃ F : P.Face,
    (pole : Space) ∈ F.val ∧ (u.val : Space) ∈ F.val ∧ (v.val : Space) ∈ F.val
  symm := by
    rintro u v ⟨different, F, poleF, uF, vF⟩
    exact ⟨different.symm, F, poleF, vF, uF⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

variable (P : ConvexPolyhedron)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include small_faces

/-- The two original facets on an edge supply its two neighbors in the local cycle. -/
theorem neighborLink_two_neighbors (pole : P.Vertex) (b : P.edgeGraph.neighborSet pole) :
    ∃ c d : P.edgeGraph.neighborSet pole, c ≠ d ∧
      (P.neighborLink pole).neighborSet b = {c, d} := by
  have edge : P.edgeGraph.Adj pole b.val := b.property
  obtain ⟨F, G, different, poleF, bF, poleG, bG, incident⟩ :=
    P.edge_incident_faces pole b.val edge
  obtain ⟨c, cb, pc, cF, inF⟩ :=
    F.exists_other_corner_neighbor (small_faces F) pole b.val b.property poleF bF
  obtain ⟨d, db, pd, dG, inG⟩ :=
    G.exists_other_corner_neighbor (small_faces G) pole b.val b.property poleG bG
  have cd : c ≠ d := by
    intro same
    exact different (F.eq_of_three_vertices G pole b.val c edge.ne pc.ne cb.symm
      poleF bF cF poleG bG (same.symm ▸ dG))
  refine ⟨⟨c, pc⟩, ⟨d, pd⟩, fun same => cd (congrArg Subtype.val same), ?_⟩
  ext w
  constructor
  · rintro ⟨different_w, H, poleH, bH, wH⟩
    have wb : w.val ≠ b.val := fun same => different_w (Subtype.ext same.symm)
    rcases incident H poleH bH with rfl | rfl
    · exact Or.inl (Subtype.ext ((inF w.val wH w.property).resolve_left wb))
    · exact Or.inr (Subtype.ext ((inG w.val wH w.property).resolve_left wb))
  · rintro (rfl | rfl)
    · exact ⟨fun same => cb (congrArg Subtype.val same).symm, F, poleF, bF, cF⟩
    · exact ⟨fun same => db (congrArg Subtype.val same).symm, G, poleG, bG, dG⟩

/-- In a solid with at most six vertices, every local face cycle is connected. -/
theorem neighborLink_connected (size : P.vertices.card ≤ 6) (pole : P.Vertex) :
    (P.neighborLink pole).Connected := by
  classical
  have lower := P.edgeGraph_min_degree pole
  have upper := Fintype.card_lt_of_injective_of_notMem
    (fun v : P.edgeGraph.neighborSet pole => v.val) Subtype.val_injective
    (b := pole) (by
      rintro ⟨v, same⟩
      have edge : P.edgeGraph.Adj pole v.val := v.property
      exact edge.ne same.symm)
  have count : Fintype.card P.Vertex = P.vertices.card := by simp [Vertex]
  rw [← Nat.card_eq_fintype_card, count] at upper
  have small_card : Nat.card (P.edgeGraph.neighborSet pole) ≤ 5 := by omega
  have card : Fintype.card (P.edgeGraph.neighborSet pole) = P.edgeGraph.degree pole :=
    SimpleGraph.card_neighborSet_eq_degree _ _
  letI : Nonempty (P.edgeGraph.neighborSet pole) := Fintype.card_pos_iff.mp (by rw [card]; omega)
  exact small_two_neighbor_graph_connected (P.neighborLink pole) (by
    simpa only [← Nat.card_eq_fintype_card] using small_card)
    (P.neighborLink_two_neighbors small_faces pole)

end SixVertexUnfolding.ConvexPolyhedron
