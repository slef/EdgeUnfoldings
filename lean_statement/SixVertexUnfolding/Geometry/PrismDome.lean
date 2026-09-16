import SixVertexUnfolding.Geometry.DomeDevelopment
import SixVertexUnfolding.Geometry.SixVertexFacets
import SixVertexUnfolding.Geometry.CommonFacetHinge

/-! A triangular prism, including one with nonparallel triangular faces, is a dome. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- Any one of the three original quadrilaterals is adjacent to all other facets. -/
theorem prism_quadrilateral_is_base
    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4)
    (kind : graph.kind = .prism) (base : P.Face)
    (quadrilateral : (base.vertexLabels graph.vertex).card = 4) :
    ∀ F : P.Face, F ≠ base → P.ShareEdge base F := by
  intro F different
  have listed (G : P.Face) : G.vertexLabels graph.vertex ∈ SmallGraphs.SixGraphKind.prism.facets := by
    rw [← kind]
    exact (graph.exists_facet_iff small_faces _).mp ⟨G, rfl⟩
  have labels_differ : F.vertexLabels graph.vertex ≠ base.vertexLabels graph.vertex :=
    fun same => different (Face.vertexLabels_injective graph.vertex same)
  have count := (by decide : ∀ A B : Finset (Fin 6),
    A ∈ SmallGraphs.SixGraphKind.prism.facets → A.card = 4 →
    B ∈ SmallGraphs.SixGraphKind.prism.facets → B ≠ A → (A ∩ B).card = 2)
      _ _ (listed base) quadrilateral (listed F) labels_differ
  obtain ⟨a, b, distinct, common⟩ := Finset.card_eq_two.mp count
  have ain : a ∈ base.vertexLabels graph.vertex ∩ F.vertexLabels graph.vertex := by rw [common]; simp
  have bin : b ∈ base.vertexLabels graph.vertex ∩ F.vertexLabels graph.vertex := by rw [common]; simp
  have segment_eq := base.intersection_eq_segment_of_common_vertices F different.symm
    (graph.vertex a) (graph.vertex b) (graph.vertex.injective.ne distinct)
    ((base.mem_vertexLabels _ a).mp (Finset.mem_inter.mp ain).1)
    ((base.mem_vertexLabels _ b).mp (Finset.mem_inter.mp bin).1)
    ((F.mem_vertexLabels _ a).mp (Finset.mem_inter.mp ain).2)
    ((F.mem_vertexLabels _ b).mp (Finset.mem_inter.mp bin).2)
  change affineDimension (base.val ∩ F.val) = 1
  rw [segment_eq, ← convexHull_pair, affineDimension_convexHull]
  exact affineDimension_pair (fun same => distinct (graph.vertex.injective (Subtype.ext same)))

/-- The original prism graph supplies a whole quadrilateral base and all four original hinges. -/
theorem exists_prism_dome
    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4)
    (kind : graph.kind = .prism) : Nonempty P.Dome := by
  have member : ({0, 1, 3, 4} : Finset (Fin 6)) ∈ graph.kind.facets := by rw [kind]; decide
  obtain ⟨base, labels⟩ := (graph.exists_facet_iff small_faces _).mpr member
  exact ⟨⟨base, graph.prism_quadrilateral_is_base small_faces kind base (by rw [labels]; decide)⟩⟩

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
