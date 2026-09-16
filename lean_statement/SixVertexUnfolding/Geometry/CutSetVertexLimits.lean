import SixVertexUnfolding.Geometry.CutSetConnected

/-! No isolated vertices were artificially added to the cut set: every
point of it is a limit of genuine multiple-shortest-route targets. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set Filter
open scoped Topology

/-- Every genuine extreme vertex belongs to the boundary. -/
theorem vertex_mem_frontier (P : ConvexPolyhedron) {v : Space} (vertex : v ∈ P.vertices) :
    v ∈ frontier P.body := by
  refine ⟨subset_closure (P.vertices_subset_body vertex), ?_⟩
  intro inside
  apply disjoint_left.mp (disjoint_interior_extremePoints P.body) inside
  rw [P.body_extreme_points]
  exact vertex

/-- At least two original vertices remain in the cut set after excluding the source. -/
theorem cutSet_nontrivial (P : ConvexPolyhedron) (a : frontier P.body) : Nontrivial (P.cutSet a) := by
  classical
  have enough : 1 < (P.vertices.erase (a : Space)).card := by
    have lower := P.four_le_vertex_count
    have bound := Finset.pred_card_le_card_erase (s := P.vertices) (a := (a : Space))
    omega
  obtain ⟨v, hv, w, hw, different⟩ := Finset.one_lt_card.mp enough
  have v_mem := (Finset.mem_erase.mp hv).2
  have w_mem := (Finset.mem_erase.mp hw).2
  let b : frontier P.body := ⟨v, P.vertex_mem_frontier v_mem⟩
  let c : frontier P.body := ⟨w, P.vertex_mem_frontier w_mem⟩
  have bcut : b ∈ P.cutSet a := Or.inr ⟨v_mem,
    fun same => (Finset.mem_erase.mp hv).1 (congrArg Subtype.val same)⟩
  have ccut : c ∈ P.cutSet a := Or.inr ⟨w_mem,
    fun same => (Finset.mem_erase.mp hw).1 (congrArg Subtype.val same)⟩
  exact ⟨⟨⟨b, bcut⟩, ⟨c, ccut⟩, fun same => different
    (congrArg (fun x : P.cutSet a => (x.val : Space)) same)⟩⟩

namespace SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- The connected cut set has no isolated points, including at original vertices. -/
theorem cutSet_no_isolated_points (a : frontier P.body) (b : P.cutSet a) : NeBot (𝓝[≠] b) := by
  letI : PathConnectedSpace (P.cutSet a) :=
    isPathConnected_iff_pathConnectedSpace.mp (graph.cutSet_pathConnected small_faces a)
  letI : Nontrivial (P.cutSet a) := P.cutSet_nontrivial a
  infer_instance

include graph small_faces in
/-- Every added original vertex is approached by actual multiple-route targets. -/
theorem cutSet_subset_closure_multiple (a : frontier P.body) :
    P.cutSet a ⊆ closure {b : frontier P.body | (b : Space) ∈ P.multipleRouteLocus a} := by
  letI : ∀ b : P.cutSet a, NeBot (𝓝[≠] b) := graph.cutSet_no_isolated_points small_faces a
  let vertices : Set (P.cutSet a) := {c | (c.val : Space) ∈ P.vertices}
  have finite : vertices.Finite := P.vertices.finite_toSet.preimage
    (show Set.InjOn (fun c : P.cutSet a => (c.val : Space)) vertices from
      (Subtype.val_injective.comp Subtype.val_injective).injOn)
  have dense : Dense (univ \ vertices) := dense_univ.diff_finite finite
  intro b cut
  apply mem_closure_iff.mpr
  intro U openU bU
  obtain ⟨c, cU, nonvertex⟩ := mem_closure_iff.mp (dense ⟨b, cut⟩)
    (Subtype.val ⁻¹' U) (openU.preimage continuous_subtype_val) bU
  refine ⟨c.val, cU, ?_⟩
  rcases c.property with multiple | vertex
  · exact multiple
  · exact False.elim (nonvertex.2 vertex.1)

include graph small_faces in
/-- The compact cut set equals precisely the closure of the multiple-route locus. -/
theorem cutSet_eq_closure_multiple (a : frontier P.body) :
    P.cutSet a = closure {b : frontier P.body | (b : Space) ∈ P.multipleRouteLocus a} :=
  subset_antisymm (graph.cutSet_subset_closure_multiple small_faces a)
    (graph.closure_multiple_subset_cutSet small_faces a)

end SixVertexGraph
end SixVertexUnfolding.ConvexPolyhedron
