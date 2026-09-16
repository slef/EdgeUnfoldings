import SixVertexUnfolding.Geometry.UniversalVertexFacets
import SixVertexUnfolding.Geometry.EdgeFacePairs
import SixVertexUnfolding.Geometry.TriangularFacets

/-! The actual face link of a universal vertex. Each neighbor has exactly
two link neighbors, supplied by the two original faces on its incident edge. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- Neighbors in the vertex link share a face with the removed source vertex. -/
def vertexLink (P : ConvexPolyhedron) (source : P.Vertex) : SimpleGraph {v : P.Vertex // v ≠ source} where
  Adj u v := u ≠ v ∧ ∃ F : P.Face,
    (source : Space) ∈ F.val ∧ (u.val : Space) ∈ F.val ∧ (v.val : Space) ∈ F.val
  symm := by
    rintro u v ⟨different, F, source, left, right⟩
    exact ⟨different.symm, F, source, right, left⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

noncomputable instance vertexLink_locallyFinite (P : ConvexPolyhedron) (source : P.Vertex) :
    (P.vertexLink source).LocallyFinite := fun _ => Fintype.ofFinite _

/-- The two incident triangular faces give exactly two distinct neighbors in the link. -/
theorem universal_vertex_link_neighbors (P : ConvexPolyhedron)
    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4)
    (source : P.Vertex) (universal : ∀ v : P.Vertex, v ≠ source → P.edgeGraph.Adj source v)
    (b : {v : P.Vertex // v ≠ source}) :
    ∃ c d : {v : P.Vertex // v ≠ source}, c ≠ d ∧ (P.vertexLink source).neighborSet b = {c, d} := by
  obtain ⟨F, G, distinct, sourceF, bF, sourceG, bG, incident⟩ :=
    P.edge_incident_faces source b.val (universal b.val b.property)
  obtain ⟨c, cs, cb, verticesF⟩ := F.exists_third_vertex
    (P.universal_vertex_facets_triangular small_faces source universal F sourceF)
    source b.val b.property.symm sourceF bF
  obtain ⟨d, ds, db, verticesG⟩ := G.exists_third_vertex
    (P.universal_vertex_facets_triangular small_faces source universal G sourceG)
    source b.val b.property.symm sourceG bG
  have memberF (w : P.Vertex) : (w : Space) ∈ F.val ↔ w = source ∨ w = b.val ∨ w = c := by
    have iff_vertices : (w : Space) ∈ F.val ↔ (w : Space) ∈ F.val ∩ (P.vertices : Set Space) :=
      ⟨fun h => ⟨h, w.property⟩, fun h => h.1⟩
    rw [iff_vertices, verticesF]
    simp only [mem_insert_iff, mem_singleton_iff, Subtype.coe_inj]
  have memberG (w : P.Vertex) : (w : Space) ∈ G.val ↔ w = source ∨ w = b.val ∨ w = d := by
    have iff_vertices : (w : Space) ∈ G.val ↔ (w : Space) ∈ G.val ∩ (P.vertices : Set Space) :=
      ⟨fun h => ⟨h, w.property⟩, fun h => h.1⟩
    rw [iff_vertices, verticesG]
    simp only [mem_insert_iff, mem_singleton_iff, Subtype.coe_inj]
  have cd : c ≠ d := by
    intro same
    apply distinct
    apply F.eq_of_same_vertices G
    rw [verticesF, verticesG, same]
  refine ⟨⟨c, cs⟩, ⟨d, ds⟩, fun same => cd (congrArg Subtype.val same), ?_⟩
  ext w
  constructor
  · rintro ⟨different, H, sourceH, bH, wH⟩
    have wb : w.val ≠ b.val := fun same => different (Subtype.ext same.symm)
    rcases incident H sourceH bH with rfl | rfl
    · have same : w.val = c := ((memberF w.val).mp wH).resolve_left w.property |>.resolve_left wb
      exact Or.inl (Subtype.ext same)
    · have same : w.val = d := ((memberG w.val).mp wH).resolve_left w.property |>.resolve_left wb
      exact Or.inr (Subtype.ext same)
  · rintro (rfl | rfl)
    · exact ⟨fun same => cb (congrArg Subtype.val same).symm,
        F, sourceF, bF, (memberF c).mpr (Or.inr (Or.inr rfl))⟩
    · exact ⟨fun same => db (congrArg Subtype.val same).symm,
        G, sourceG, bG, (memberG d).mpr (Or.inr (Or.inr rfl))⟩

/-- The actual universal-vertex link is two-regular. -/
theorem universal_vertex_link_degree (P : ConvexPolyhedron)
    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4)
    (source : P.Vertex) (universal : ∀ v : P.Vertex, v ≠ source → P.edgeGraph.Adj source v)
    (b : {v : P.Vertex // v ≠ source}) : (P.vertexLink source).degree b = 2 := by
  obtain ⟨c, d, distinct, neighbors⟩ := P.universal_vertex_link_neighbors small_faces source universal b
  rw [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card,
    Nat.card_coe_set_eq, neighbors, Set.ncard_pair distinct]

end SixVertexUnfolding.ConvexPolyhedron
