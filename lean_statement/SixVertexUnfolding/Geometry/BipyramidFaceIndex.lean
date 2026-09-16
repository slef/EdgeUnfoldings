import SixVertexUnfolding.Geometry.BipyramidFacets

/-!
Index the six original facets by a pole and the omitted equator vertex.
This small index is used only inside the proof, keeping the public statement unchanged.
-/

namespace SixVertexUnfolding.ConvexPolyhedron.BipyramidVertices

variable {P : ConvexPolyhedron} (B : BipyramidVertices P)

/-- A face at one pole contains the other two equator vertices. -/
def faceVertices (upper : Bool) (missing : Fin 3) : Set Space :=
  insert (B.poleVertex upper : Space)
    ((fun i : Fin 3 => (B.equatorVertex i : Space)) '' {i | i ≠ missing})

theorem equator_complement_pair (missing : Fin 3) :
    ∃ i j : Fin 3, i ≠ j ∧ {k : Fin 3 | k ≠ missing} = {i, j} := by
  fin_cases missing
  · exact ⟨1, 2, by decide, by ext k; fin_cases k <;> decide⟩
  · exact ⟨0, 2, by decide, by ext k; fin_cases k <;> decide⟩
  · exact ⟨0, 1, by decide, by ext k; fin_cases k <;> decide⟩

/-- Every index describes an actual original facet. -/
theorem exists_indexed_face
    (triangles : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3)
    (upper : Bool) (missing : Fin 3) :
    ∃ F : P.Face, F.val ∩ (P.vertices : Set Space) = B.faceVertices upper missing := by
  obtain ⟨i, j, different, pair⟩ := equator_complement_pair missing
  obtain ⟨F, vertices⟩ := B.exists_pole_facet triangles upper i j different
  refine ⟨F, ?_⟩
  simpa only [faceVertices, pair, Set.image_insert_eq, Set.image_singleton] using vertices

/-- The original facet at one pole, opposite one equator vertex. -/
noncomputable def face
    (triangles : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3)
    (upper : Bool) (missing : Fin 3) : P.Face := (B.exists_indexed_face triangles upper missing).choose

theorem face_vertices
    (triangles : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3)
    (upper : Bool) (missing : Fin 3) :
    (B.face triangles upper missing).val ∩ (P.vertices : Set Space) = B.faceVertices upper missing :=
  (B.exists_indexed_face triangles upper missing).choose_spec

/-- The cyclic indices used for corner angles are precisely the three original facet vertices. -/
theorem face_vertices_cyclic
    (triangles : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3)
    (upper : Bool) (missing : Fin 3) :
    (B.face triangles upper missing).val ∩ (P.vertices : Set Space) =
      {(B.poleVertex upper : Space), (B.equatorVertex (missing + 1) : Space),
        (B.equatorVertex (missing + 2) : Space)} := by
  have pair : {j : Fin 3 | j ≠ missing} = {missing + 1, missing + 2} := by
    fin_cases missing <;> ext j <;> fin_cases j <;> decide
  rw [B.face_vertices, faceVertices, pair, Set.image_insert_eq, Set.image_singleton]

theorem pole_mem_face
    (triangles : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3)
    (upper : Bool) (missing : Fin 3) :
    (B.poleVertex upper : Space) ∈ (B.face triangles upper missing).val := by
  have member : (B.poleVertex upper : Space) ∈
      (B.face triangles upper missing).val ∩ (P.vertices : Set Space) := by
    rw [B.face_vertices]
    exact Or.inl rfl
  exact member.1

theorem opposite_pole_not_mem_face
    (triangles : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3)
    (upper : Bool) (missing : Fin 3) :
    (B.poleVertex (!upper) : Space) ∉ (B.face triangles upper missing).val := by
  intro member
  have edge := (B.face triangles upper missing).adjacent_of_triangle
    (triangles _) (B.poleVertex upper) (B.poleVertex (!upper))
    (B.pole_ne_opposite upper) (B.pole_mem_face triangles upper missing) member
  exact B.pole_opposite_not_adjacent upper edge

/-- Membership of an equator vertex is exactly inequality with the omitted index. -/
theorem equator_mem_face
    (triangles : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3)
    (upper : Bool) (missing i : Fin 3) :
    (B.equatorVertex i : Space) ∈ (B.face triangles upper missing).val ↔ i ≠ missing := by
  constructor
  · intro member
    have in_vertices : (B.equatorVertex i : Space) ∈
        (B.face triangles upper missing).val ∩ (P.vertices : Set Space) := ⟨member, (B.equatorVertex i).property⟩
    rw [B.face_vertices] at in_vertices
    rcases in_vertices with at_pole | ⟨j, different, equal⟩
    · exact False.elim (B.pole_ne_equator upper i (Subtype.ext at_pole.symm))
    · have ji : j = i := B.equator_injective (Subtype.ext equal)
      exact ji ▸ different
  · intro different
    have member : (B.equatorVertex i : Space) ∈
        (B.face triangles upper missing).val ∩ (P.vertices : Set Space) := by
      rw [B.face_vertices]
      exact Or.inr ⟨i, different, rfl⟩
    exact member.1

/-- The six face indices have no duplicates. -/
theorem face_index_injective
    (triangles : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3) :
    Function.Injective (fun index : Bool × Fin 3 => B.face triangles index.1 index.2) := by
  rintro ⟨upper, i⟩ ⟨lower, j⟩ same
  change B.face triangles upper i = B.face triangles lower j at same
  have poles : upper = lower := by
    by_contra different
    have opposite : lower = !upper := by cases upper <;> cases lower <;> simp_all
    have member := B.pole_mem_face triangles lower j
    rw [← same, opposite] at member
    exact B.opposite_pole_not_mem_face triangles upper i member
  subst lower
  have indices : i = j := by
    by_contra different
    have member := (B.equator_mem_face triangles upper j i).mpr different
    rw [← same] at member
    exact (B.equator_mem_face triangles upper i i).mp member rfl
  exact Prod.ext rfl indices

/-- No original facets are omitted by the six face indices. -/
theorem face_index_surjective
    (triangles : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3) :
    Function.Surjective (fun index : Bool × Fin 3 => B.face triangles index.1 index.2) := by
  intro F
  have some_pole : ∃ upper : Bool, (B.poleVertex upper : Space) ∈ F.val := by
    rcases B.every_facet_contains_pole triangles F with top | bottom
    · exact ⟨true, top⟩
    · exact ⟨false, bottom⟩
  obtain ⟨upper, pole_in⟩ := some_pole
  obtain ⟨i, j, different, vertices⟩ := B.facet_at_pole triangles upper F pole_in
  have missing : ∃ k : Fin 3, k ≠ i ∧ k ≠ j := by
    fin_cases i <;> fin_cases j <;> first
      | exact False.elim (different rfl)
      | exact ⟨0, by decide, by decide⟩
      | exact ⟨1, by decide, by decide⟩
      | exact ⟨2, by decide, by decide⟩
  obtain ⟨k, ki, kj⟩ := missing
  have pair : {l : Fin 3 | l ≠ k} = {i, j} := by
    ext l
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  refine ⟨(upper, k), ?_⟩
  apply (B.face triangles upper k).eq_of_same_vertices F
  rw [B.face_vertices, faceVertices, pair, Set.image_insert_eq, Set.image_singleton, vertices]

include B in
/-- The original surface of a triangular five-vertex solid has exactly six facets. -/
theorem six_facets
    (triangles : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3) : Nat.card P.Face = 6 := by
  have equivalent := Equiv.ofBijective (fun index : Bool × Fin 3 => B.face triangles index.1 index.2)
    ⟨B.face_index_injective triangles, B.face_index_surjective triangles⟩
  rw [← Nat.card_congr equivalent]
  simp [Nat.card_eq_fintype_card]

end SixVertexUnfolding.ConvexPolyhedron.BipyramidVertices
