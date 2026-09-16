import SixVertexUnfolding.Geometry.PrismDome
import SixVertexUnfolding.Geometry.DomeSharedCorner

/-! The ordinary prism's whole-face flower has only two opposite-petal comparisons left. -/

namespace SixVertexUnfolding

namespace PrismFlower

/-- One quadrilateral base, followed by its four neighbors in boundary order. -/
def labels : Fin 5 → Finset (Fin 6) :=
  ![{0, 1, 3, 4}, {0, 2, 3, 5}, {1, 3, 5}, {1, 2, 4, 5}, {0, 2, 4}]

/-- At each consecutive pair: the base corner, two base neighbors, and the third edge endpoint. -/
def corner : Fin 4 → Fin 4 → Fin 6 :=
  ![![3, 0, 1, 5], ![1, 3, 4, 5], ![4, 1, 0, 2], ![0, 4, 3, 2]]

theorem labels_injective : Function.Injective labels := by decide

theorem labels_mem_facets : ∀ i, labels i ∈ SmallGraphs.SixGraphKind.prism.facets := by decide

set_option maxRecDepth 10000 in
theorem labels_exhaust : ∀ face : Finset (Fin 6), face ∈ SmallGraphs.SixGraphKind.prism.facets →
    ∃ i, labels i = face := by decide

set_option maxRecDepth 10000 in
theorem corner_data : ∀ i : Fin 4,
    let o := corner i 0; let a := corner i 1; let b := corner i 2; let d := corner i 3
    o ≠ a ∧ o ≠ b ∧
    o ∈ labels 0 ∧ a ∈ labels 0 ∧ b ∈ labels 0 ∧
    o ∈ labels i.succ ∧ a ∈ labels i.succ ∧ d ∈ labels i.succ ∧
    o ∈ labels (i + 1).succ ∧ b ∈ labels (i + 1).succ ∧ d ∈ labels (i + 1).succ ∧
    d ∉ labels 0 ∧ a ∉ labels (i + 1).succ ∧ b ∉ labels i.succ := by decide

theorem petal_pair_cases : ∀ i j : Fin 4, i ≠ j →
    j = i + 1 ∨ i = j + 1 ∨
    (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) ∨ (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1) := by decide

end PrismFlower

namespace ConvexPolyhedron.SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
variable (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4) (kind : graph.kind = .prism)

/-- The five positions are actual whole original facets. -/
noncomputable def prismFace (i : Fin 5) : P.Face :=
  Classical.choose ((graph.exists_facet_iff small_faces _).mpr
    (by rw [kind]; exact PrismFlower.labels_mem_facets i))

theorem prismFace_labels (i : Fin 5) :
    (graph.prismFace small_faces kind i).vertexLabels graph.vertex = PrismFlower.labels i :=
  Classical.choose_spec ((graph.exists_facet_iff small_faces _).mpr
    (by rw [kind]; exact PrismFlower.labels_mem_facets i))

theorem prismFace_injective : Function.Injective (graph.prismFace small_faces kind) := by
  intro i j same
  apply PrismFlower.labels_injective
  rw [← graph.prismFace_labels small_faces kind i, ← graph.prismFace_labels small_faces kind j, same]

theorem prismFace_surjective : Function.Surjective (graph.prismFace small_faces kind) := by
  intro F
  have listed : F.vertexLabels graph.vertex ∈ SmallGraphs.SixGraphKind.prism.facets := by
    rw [← kind]
    exact (graph.exists_facet_iff small_faces _).mp ⟨F, rfl⟩
  obtain ⟨i, same⟩ := PrismFlower.labels_exhaust _ listed
  refine ⟨i, Face.vertexLabels_injective graph.vertex ?_⟩
  change (graph.prismFace small_faces kind i).vertexLabels graph.vertex = F.vertexLabels graph.vertex
  rw [graph.prismFace_labels small_faces kind]
  exact same

/-- The flower base is the first whole quadrilateral, with four original side hinges. -/
noncomputable def prismDome : P.Dome where
  base := graph.prismFace small_faces kind 0
  side_shares_base := graph.prism_quadrilateral_is_base small_faces kind _
    (by rw [graph.prismFace_labels small_faces kind]; decide)

/-- Each consecutive pair of whole petals is separated by the actual trihedral corner argument. -/
theorem prism_consecutive_petals (net : (graph.prismDome small_faces kind).Development) (i : Fin 4) :
    Disjoint (interior (net.place (graph.prismFace small_faces kind i.succ) ''
      (graph.prismFace small_faces kind i.succ).val))
      (interior (net.place (graph.prismFace small_faces kind (i + 1).succ) ''
        (graph.prismFace small_faces kind (i + 1).succ).val)) := by
  have member (j : Fin 5) (v : Fin 6) :
      (graph.vertex v : Space) ∈ (graph.prismFace small_faces kind j).val ↔ v ∈ PrismFlower.labels j := by
    rw [← Face.mem_vertexLabels, graph.prismFace_labels small_faces kind]
  obtain ⟨oa, ob, oB, aB, bB, oF, aF, dF, oG, bG, dG, dB, aG, bF⟩ := PrismFlower.corner_data i
  apply net.shared_corner_nonoverlap _ _
    (fun same => (Fin.succ_ne_zero i) (graph.prismFace_injective small_faces kind same))
    (fun same => (Fin.succ_ne_zero (i + 1)) (graph.prismFace_injective small_faces kind same))
    (graph.vertex (PrismFlower.corner i 0)) (graph.vertex (PrismFlower.corner i 1))
    (graph.vertex (PrismFlower.corner i 2)) (graph.vertex (PrismFlower.corner i 3))
    (graph.vertex.injective.ne oa) (graph.vertex.injective.ne ob)
  · exact (member 0 _).mpr oB
  · exact (member 0 _).mpr aB
  · exact (member 0 _).mpr bB
  · exact (member i.succ _).mpr oF
  · exact (member i.succ _).mpr aF
  · exact (member i.succ _).mpr dF
  · exact (member (i + 1).succ _).mpr oG
  · exact (member (i + 1).succ _).mpr bG
  · exact (member (i + 1).succ _).mpr dG
  · exact fun inside => dB ((member 0 _).mp inside)
  · exact fun inside => aG ((member (i + 1).succ _).mp inside)
  · exact fun inside => bF ((member i.succ _).mp inside)

/-- All base pairs and all four neighboring petal pairs are proved; only the two opposite pairs are hypotheses. -/
theorem prism_unfolding_of_two_pairs (net : (graph.prismDome small_faces kind).Development)
    (quadrilaterals : Disjoint
      (interior (net.place (graph.prismFace small_faces kind 1) '' (graph.prismFace small_faces kind 1).val))
      (interior (net.place (graph.prismFace small_faces kind 3) '' (graph.prismFace small_faces kind 3).val)))
    (triangles : Disjoint
      (interior (net.place (graph.prismFace small_faces kind 2) '' (graph.prismFace small_faces kind 2).val))
      (interior (net.place (graph.prismFace small_faces kind 4) '' (graph.prismFace small_faces kind 4).val))) :
    P.HasEdgeUnfolding := by
  apply net.hasEdgeUnfolding
  intro F G F_side G_side different
  obtain ⟨i, rfl⟩ := graph.prismFace_surjective small_faces kind F
  obtain ⟨j, rfl⟩ := graph.prismFace_surjective small_faces kind G
  have i_nonzero : i ≠ 0 := fun same => F_side (congrArg (graph.prismFace small_faces kind) same)
  have j_nonzero : j ≠ 0 := fun same => G_side (congrArg (graph.prismFace small_faces kind) same)
  obtain ⟨i, rfl⟩ := Fin.eq_succ_of_ne_zero i_nonzero
  obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero j_nonzero
  have ij : i ≠ j := fun same => different (congrArg (fun k : Fin 4 => graph.prismFace small_faces kind k.succ) same)
  rcases PrismFlower.petal_pair_cases i j ij with rfl | rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact graph.prism_consecutive_petals small_faces kind net i
  · exact (graph.prism_consecutive_petals small_faces kind net j).symm
  · exact quadrilaterals
  · exact quadrilaterals.symm
  · exact triangles
  · exact triangles.symm

end ConvexPolyhedron.SixVertexGraph
end SixVertexUnfolding
