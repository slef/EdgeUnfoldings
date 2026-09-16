import SixVertexUnfolding.Geometry.BipyramidDual

/-! Retain the four cap-base hinges and the one equator hinge between the two bases. -/

namespace SixVertexUnfolding

/-- Two three-face stars joined at their centers. The second coordinate names the omitted vertex. -/
def bipyramidStar (source : Fin 3) : SimpleGraph (Bool × Fin 3) where
  Adj x y := x ≠ y ∧
    ((x.1 = y.1 ∧ (x.2 = source ∨ y.2 = source)) ∨ (x.2 = source ∧ y.2 = source))
  symm := by
    rintro x y ⟨different, same_cap | bases⟩
    · exact ⟨different.symm, Or.inl ⟨same_cap.1.symm, same_cap.2.symm⟩⟩
    · exact ⟨different.symm, Or.inr bases.symm⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance (source : Fin 3) : DecidableRel (bipyramidStar source).Adj := by
  unfold bipyramidStar
  infer_instance

theorem bipyramidStar_connected (source : Fin 3) : (bipyramidStar source).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨(true, source), ?_⟩
  rintro ⟨upper, i⟩
  have center : (bipyramidStar source).Reachable (true, source) (upper, source) := by
    cases upper
    · exact (show (bipyramidStar source).Adj (true, source) (false, source) from
        ⟨by simp, Or.inr ⟨rfl, rfl⟩⟩).reachable
    · exact SimpleGraph.Reachable.rfl
  by_cases base : i = source
  · subst i
    exact center
  · apply center.trans
    exact (show (bipyramidStar source).Adj (upper, source) (upper, i) from
      ⟨fun same => base (congrArg Prod.snd same).symm, Or.inl ⟨rfl, Or.inl rfl⟩⟩).reachable

/-- The five prescribed hinges form a tree; no further hinge choice is necessary. -/
theorem bipyramidStar_isTree (source : Fin 3) : (bipyramidStar source).IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨bipyramidStar_connected source, ?_⟩
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, Nat.card_eq_fintype_card]
  fin_cases source <;> decide

namespace ConvexPolyhedron.BipyramidVertices

variable {P : ConvexPolyhedron} (B : BipyramidVertices P)

/-- The prescribed net cuts exactly the original edges incident to the source. -/
theorem star_iff_avoid_source
    (triangles : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3)
    (source : Fin 3) (upper lower : Bool) (i j : Fin 3) :
    (bipyramidStar source).Adj (upper, i) (lower, j) ↔
      P.ShareEdge (B.face triangles upper i) (B.face triangles lower j) ∧
      (B.equatorVertex source : Space) ∉
        (B.face triangles upper i).val ∩ (B.face triangles lower j).val := by
  rw [B.face_shareEdge_iff]
  simp only [Set.mem_inter_iff, B.equator_mem_face]
  change ((upper, i) ≠ (lower, j) ∧
    ((upper = lower ∧ (i = source ∨ j = source)) ∨ (i = source ∧ j = source))) ↔ _
  simp only [ne_eq, Prod.mk.injEq]
  grind

/-- Transport the six concrete face indices to the public face type. -/
noncomputable def faceEquiv
    (triangles : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3) :
    (Bool × Fin 3) ≃ P.Face :=
  Equiv.ofBijective (fun index => B.face triangles index.1 index.2)
    ⟨B.face_index_injective triangles, B.face_index_surjective triangles⟩

/-- The indexed hinges admit a spanning tree consisting of original edges. -/
theorem exists_star_hinge_tree
    (triangles : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3) (source : Fin 3) :
    ∃ hinges : SimpleGraph P.Face, hinges.IsTree ∧ hinges ≤ P.dualGraph ∧
      ∀ F G, hinges.Adj F G →
        (bipyramidStar source).Adj ((B.faceEquiv triangles).symm F) ((B.faceEquiv triangles).symm G) := by
  let index := B.faceEquiv triangles
  let star := (bipyramidStar source).comap index.symm
  have tree : star.IsTree :=
    (SimpleGraph.Iso.comap index.symm (bipyramidStar source)).isTree_iff.mpr
      (bipyramidStar_isTree source)
  refine ⟨star, tree, ?_, fun _ _ edge => edge⟩
  intro F G edge
  have indexed := edge
  obtain ⟨⟨upper, i⟩, rfl⟩ := index.surjective F
  obtain ⟨⟨lower, j⟩, rfl⟩ := index.surjective G
  change (bipyramidStar source).Adj (index.symm (index (upper, i)))
    (index.symm (index (lower, j))) at indexed
  rw [index.symm_apply_apply, index.symm_apply_apply] at indexed
  change P.ShareEdge (B.face triangles upper i) (B.face triangles lower j)
  obtain ⟨different, same_cap | bases⟩ := indexed
  · have poles : upper = lower := same_cap.1
    subst lower
    exact B.same_cap_shareEdge triangles upper i j (fun same => different (Prod.ext rfl same))
  · have isource : i = source := bases.1
    have jsource : j = source := bases.2
    subst i
    subst j
    have opposite : lower = !upper := by
      cases upper <;> cases lower <;> simp_all
    rw [opposite]
    exact B.across_equator_shareEdge triangles upper source

end ConvexPolyhedron.BipyramidVertices
end SixVertexUnfolding
