import SixVertexUnfolding.Geometry.MultipleShortestRoutes

/-! The finite candidate lines have empty interior. Their complement is
open and dense, and the multiple-route locus is nowhere dense inside a face. -/

namespace SixVertexUnfolding

open Set

/-- A planar line with nonzero normal has empty ordinary planar interior. -/
theorem line_interior_empty (normal : Plane) (nonzero : normal ≠ 0) (c : ℝ) :
    interior {x : Plane | inner ℝ normal x = c} = ∅ := by
  change interior ((innerSL ℝ normal) ⁻¹' {c}) = ∅
  rw [(innerSL ℝ normal).interior_preimage (plane_inner_height_surjective nonzero),
    interior_singleton, preimage_empty]

/-- Finitely many closed sets with empty interior still have empty interior together. -/
theorem finite_closed_sUnion_interior_empty (sets : Set (Set Plane)) (finite : sets.Finite)
    (closed : ∀ s ∈ sets, IsClosed s) (empty : ∀ s ∈ sets, interior s = ∅) :
    interior (⋃₀ sets) = ∅ := by
  revert closed empty
  induction sets, finite using Set.Finite.induction_on with
  | empty => simp
  | @insert s sets absent finite ih =>
      intro closed empty
      have remaining := ih (fun t ht => closed t (Or.inr ht)) (fun t ht => empty t (Or.inr ht))
      rw [sUnion_insert, interior_union_isClosed_of_interior_empty (closed s (Or.inl rfl)) remaining]
      exact empty s (Or.inl rfl)

namespace ConvexPolyhedron

theorem sourceBisectors_union_interior_empty (P : ConvexPolyhedron) (a : Space) (F : P.Face) :
    interior (⋃₀ P.sourceBisectors a F) = ∅ := by
  apply finite_closed_sUnion_interior_empty _ (P.sourceBisectors_finite a F) (P.sourceBisector_closed a F)
  intro line member
  obtain ⟨normal, nonzero, c, rfl⟩ := P.sourceBisector_equation a F line member
  exact line_interior_empty normal nonzero c

/-- Away from a closed finite arrangement of lines is an open dense planar region. -/
theorem sourceBisectors_complement_open_dense (P : ConvexPolyhedron) (a : Space) (F : P.Face) :
    IsOpen (⋃₀ P.sourceBisectors a F)ᶜ ∧ Dense (⋃₀ P.sourceBisectors a F)ᶜ :=
  ⟨(P.sourceBisectors_union_closed a F).isOpen_compl,
    interior_eq_empty_iff_dense_compl.mp (P.sourceBisectors_union_interior_empty a F)⟩

namespace SixVertexGraph

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- Multiple-route targets in a unique-face region have nowhere-dense planar coordinates. -/
theorem multiple_routes_nowhere_dense_in_face (a : Space) (F : P.Face) :
    interior (closure (P.faceCoordinates F ''
      {b | b ∈ P.multipleRouteLocus a ∧ ∀ G : P.Face, b ∈ G.val → G = F})) = ∅ := by
  have contained : P.faceCoordinates F ''
      {b | b ∈ P.multipleRouteLocus a ∧ ∀ G : P.Face, b ∈ G.val → G = F} ⊆ ⋃₀ P.sourceBisectors a F := by
    rintro x ⟨b, hb, rfl⟩
    exact graph.multiple_routes_on_source_bisectors small_faces hb.1 F hb.2
  have closure_contained := closure_minimal contained (P.sourceBisectors_union_closed a F)
  exact subset_empty_iff.mp ((interior_mono closure_contained).trans_eq (P.sourceBisectors_union_interior_empty a F))

end SixVertexGraph
end ConvexPolyhedron
end SixVertexUnfolding
