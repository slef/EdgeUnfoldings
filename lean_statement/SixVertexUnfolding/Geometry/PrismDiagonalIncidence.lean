import SixVertexUnfolding.Geometry.PrismDiagonalFaces
import SixVertexUnfolding.Geometry.CommonFacetHinge
import SixVertexUnfolding.Geometry.TreeDevelopment

/-! Exact original-face incidence for the prism candidates. In particular, the
fallback retains C-A, C-B, C-E, E-D, E-F, all along original edges. -/

namespace SixVertexUnfolding.Prism

open FaceLabel

/-- The five retained hinges of the fixed fallback, in the paper's face labels. -/
def fallbackHinges : SimpleGraph FaceLabel where
  Adj f g := s(f, g) ∈ ({s(C, A), s(C, B), s(C, E), s(E, D), s(E, F)} : Finset (Sym2 FaceLabel))
  symm := by
    intro f g h
    simpa only [Sym2.eq_swap] using h
  loopless := ⟨by intro f; cases f <;> decide⟩

instance : DecidableRel fallbackHinges.Adj := by unfold fallbackHinges; infer_instance

theorem fallbackHinges_connected : fallbackHinges.Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨C, ?_⟩
  intro f
  have CE : fallbackHinges.Reachable C E := (show fallbackHinges.Adj C E from by decide).reachable
  cases f
  · exact (show fallbackHinges.Adj C A from by decide).reachable
  · exact (show fallbackHinges.Adj C B from by decide).reachable
  · exact SimpleGraph.Reachable.rfl
  · exact CE.trans (show fallbackHinges.Adj E D from by decide).reachable
  · exact CE
  · exact CE.trans (show fallbackHinges.Adj E F from by decide).reachable

theorem fallbackHinges_isTree : fallbackHinges.IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨fallbackHinges_connected, ?_⟩
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, Nat.card_eq_fintype_card]
  decide

end SixVertexUnfolding.Prism

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Prism Prism.FaceLabel

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
variable (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4)
variable (prism_kind : graph.kind = .prismDiagonal)
include small_faces prism_kind

/-- The six manuscript labels enumerate all whole original faces exactly once. -/
theorem prismDiagonalFace_bijective : Function.Bijective (graph.prismDiagonalFace small_faces) := by
  constructor
  · intro f g same
    have labels := congrArg (fun F : P.Face => F.vertexLabels graph.vertex) same
    dsimp only at labels
    rw [graph.prismDiagonalFace_labels small_faces prism_kind,
      graph.prismDiagonalFace_labels small_faces prism_kind] at labels
    exact (by decide : Function.Injective (fun f => (faceVertices f).image vertexLabel)) labels
  · intro F
    have member := (graph.exists_facet_iff small_faces (F.vertexLabels graph.vertex)).mp ⟨F, rfl⟩
    rw [prism_kind] at member
    obtain ⟨f, labels⟩ := (by decide : ∀ vertices : Finset (Fin 6),
      vertices ∈ SmallGraphs.SixGraphKind.prismDiagonal.facets →
      ∃ f, (faceVertices f).image vertexLabel = vertices) _ member
    refine ⟨f, Face.vertexLabels_injective graph.vertex ?_⟩
    dsimp only
    rw [graph.prismDiagonalFace_labels small_faces prism_kind, labels]

/-- The sources needed by both near-stars and the fallback comparison are cofacial
with every original vertex, so the proved cofacial star theorem applies. -/
theorem prism_cofacial_sources (source : Fin 6)
    (eligible : source = 1 ∨ source = 2 ∨ source = 3 ∨ source = 5) :
    ∀ v : P.Vertex, ∃ F : P.Face, (graph.prismVertex source : Space) ∈ F.val ∧ (v : Space) ∈ F.val := by
  intro v
  obtain ⟨i, rfl⟩ := (vertexLabel.trans graph.vertex).surjective v
  obtain ⟨f, first, second⟩ := (by decide : ∀ source i : Fin 6,
    (source = 1 ∨ source = 2 ∨ source = 3 ∨ source = 5) →
    ∃ f, source ∈ faceVertices f ∧ i ∈ faceVertices f) source i eligible
  exact ⟨graph.prismDiagonalFace small_faces f,
    (graph.prismVertex_mem_face small_faces prism_kind f source).mpr first,
    (graph.prismVertex_mem_face small_faces prism_kind f i).mpr second⟩

/-- Every retained fallback adjacency is a whole original edge. -/
theorem prism_fallback_original_hinge (f g : FaceLabel) (hinge : fallbackHinges.Adj f g) :
    P.ShareEdge (graph.prismDiagonalFace small_faces f) (graph.prismDiagonalFace small_faces g) := by
  have different := (graph.prismDiagonalFace_bijective small_faces prism_kind).1.ne hinge.ne
  obtain ⟨a, b, ab, af, bf, ag, bg⟩ := (by decide : ∀ f g, fallbackHinges.Adj f g →
    ∃ a b : Fin 6, a ≠ b ∧ a ∈ faceVertices f ∧ b ∈ faceVertices f ∧
      a ∈ faceVertices g ∧ b ∈ faceVertices g) f g hinge
  have segment_eq := (graph.prismDiagonalFace small_faces f).intersection_eq_segment_of_common_vertices
    (graph.prismDiagonalFace small_faces g) different (graph.prismVertex a) (graph.prismVertex b)
    (graph.vertex.injective.ne (vertexLabel.injective.ne ab))
    ((graph.prismVertex_mem_face small_faces prism_kind f a).mpr af)
    ((graph.prismVertex_mem_face small_faces prism_kind f b).mpr bf)
    ((graph.prismVertex_mem_face small_faces prism_kind g a).mpr ag)
    ((graph.prismVertex_mem_face small_faces prism_kind g b).mpr bg)
  change affineDimension _ = 1
  rw [segment_eq, ← convexHull_pair, affineDimension_convexHull]
  exact affineDimension_pair (graph.prismVertex_injective.ne ab)

/-- Transport the paper's six face labels to the public type of all original faces. -/
noncomputable def prismDiagonalFaceEquiv : FaceLabel ≃ P.Face :=
  Equiv.ofBijective (graph.prismDiagonalFace small_faces) (graph.prismDiagonalFace_bijective small_faces prism_kind)

/-- The fixed fallback already supplies a tree of original hinges on the actual solid. -/
theorem exists_prism_fallback_hinges :
    ∃ hinges : SimpleGraph P.Face, hinges.IsTree ∧ hinges ≤ P.dualGraph ∧
      ∀ f g, hinges.Adj (graph.prismDiagonalFace small_faces f) (graph.prismDiagonalFace small_faces g) ↔
        fallbackHinges.Adj f g := by
  let index := graph.prismDiagonalFaceEquiv small_faces prism_kind
  let hinges := fallbackHinges.comap index.symm
  have tree : hinges.IsTree :=
    (SimpleGraph.Iso.comap index.symm fallbackHinges).isTree_iff.mpr fallbackHinges_isTree
  have original : hinges ≤ P.dualGraph := by
    intro F G edge
    obtain ⟨f, rfl⟩ := index.surjective F
    obtain ⟨g, rfl⟩ := index.surjective G
    change fallbackHinges.Adj (index.symm (index f)) (index.symm (index g)) at edge
    rw [index.symm_apply_apply, index.symm_apply_apply] at edge
    exact graph.prism_fallback_original_hinge small_faces prism_kind f g edge
  refine ⟨hinges, tree, original, ?_⟩
  intro f g
  change fallbackHinges.Adj (index.symm (index f)) (index.symm (index g)) ↔ _
  rw [index.symm_apply_apply, index.symm_apply_apply]

/-- A rigid hinge-aligned placement exists for this prescribed tree.
Choosing the outward placement and proving nonoverlap remain separate obligations. -/
theorem exists_prism_fallback_rigid_placement :
    ∃ (hinges : SimpleGraph P.Face) (place : P.Face → Space →ᵃ[ℝ] Plane),
      hinges.IsTree ∧ hinges ≤ P.dualGraph ∧
      (∀ f g, hinges.Adj (graph.prismDiagonalFace small_faces f) (graph.prismDiagonalFace small_faces g) ↔
        fallbackHinges.Adj f g) ∧
      (∀ F, ∀ x ∈ F.val, ∀ y ∈ F.val, dist (place F x) (place F y) = dist x y) ∧
      (∀ F G, hinges.Adj F G → ∀ x ∈ F.val ∩ G.val, place F x = place G x) := by
  obtain ⟨hinges, tree, original, named⟩ := graph.exists_prism_fallback_hinges small_faces prism_kind
  obtain ⟨place, rigid, joined⟩ := exists_tree_development P hinges tree original
  exact ⟨hinges, place, tree, original, named, rigid, joined⟩

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
