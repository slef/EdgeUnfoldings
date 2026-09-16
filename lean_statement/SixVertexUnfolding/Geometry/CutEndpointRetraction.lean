import SixVertexUnfolding.Geometry.UniqueCutEndpoint
import SixVertexUnfolding.Geometry.CutSetInSpace
import SixVertexUnfolding.Geometry.SurfaceTopology

/-! Extending rays defines a continuous retraction of the punctured boundary
onto the actual cut set. Compactness and uniqueness prove continuity. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

/-- Follow the shortest ray to its unique terminal cut point. -/
noncomputable def cutEndpoint (a : frontier P.body) (b : {b : frontier P.body // b ≠ a}) : P.cutSet a :=
  ⟨(graph.exists_shortest_extension_in_cutSet small_faces a b.val b.property.symm).choose,
    (graph.exists_shortest_extension_in_cutSet small_faces a b.val b.property.symm).choose_spec.1⟩

theorem cutEndpoint_extension (a : frontier P.body) (b : {b : frontier P.body // b ≠ a}) :
    (graph.cutEndpoint small_faces a b).val ∈ P.shortestExtensions a b.val :=
  (graph.exists_shortest_extension_in_cutSet small_faces a b.val b.property.symm).choose_spec.2

/-- Cut points themselves are fixed by the endpoint map. -/
theorem cutEndpoint_fixes (a : frontier P.body) (c : P.cutSet a) :
    graph.cutEndpoint small_faces a ⟨c.val, ne_of_mem_of_not_mem c.property (P.source_not_cutSet a)⟩ = c := by
  apply Subtype.ext
  exact graph.shortest_extension_of_cut_point small_faces a c.val _ c.property
    (graph.cutEndpoint_extension small_faces a _)

/-- The terminal endpoint depends continuously on the point being extended. -/
theorem cutEndpoint_continuous (a : frontier P.body) : Continuous (graph.cutEndpoint small_faces a) := by
  let X := {b : frontier P.body // b ≠ a}
  let Y := P.cutSet a
  letI : CompactSpace Y := isCompact_iff_compactSpace.mp (graph.cutSet_compact small_faces a)
  let relation : Set (X × Y) := {p | p.2.val ∈ P.shortestExtensions a p.1.val}
  have first : Continuous (fun p : X × Y => p.1.val) := continuous_subtype_val.comp continuous_fst
  have second : Continuous (fun p : X × Y => p.2.val) := continuous_subtype_val.comp continuous_snd
  have closed_relation : IsClosed relation := isClosed_eq
    (P.surfaceDist_continuous.comp (continuous_const.prodMk second))
    ((P.surfaceDist_continuous.comp (continuous_const.prodMk first)).add
      (P.surfaceDist_continuous.comp (first.prodMk second)))
  apply continuous_iff_isClosed.mpr
  intro C closedC
  have equality : (graph.cutEndpoint small_faces a) ⁻¹' C =
      Prod.fst '' (relation ∩ Prod.snd ⁻¹' C) := by
    ext b
    constructor
    · intro member
      exact ⟨(b, graph.cutEndpoint small_faces a b),
        ⟨graph.cutEndpoint_extension small_faces a b, member⟩, rfl⟩
    · rintro ⟨⟨d, c⟩, ⟨extension, member⟩, same⟩
      change d = b at same
      subst d
      have equal : c = graph.cutEndpoint small_faces a b := Subtype.ext
        (graph.cut_endpoint_unique small_faces a b.val c.val _ b.property.symm
          c.property (graph.cutEndpoint small_faces a b).property extension
          (graph.cutEndpoint_extension small_faces a b))
      rwa [equal] at member
  rw [equality]
  exact isClosedMap_fst_of_compactSpace _ (closed_relation.inter (closedC.preimage continuous_snd))

theorem cutEndpoint_surjective (a : frontier P.body) : Function.Surjective (graph.cutEndpoint small_faces a) := by
  intro c
  exact ⟨⟨c.val, ne_of_mem_of_not_mem c.property (P.source_not_cutSet a)⟩,
    graph.cutEndpoint_fixes small_faces a c⟩

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
