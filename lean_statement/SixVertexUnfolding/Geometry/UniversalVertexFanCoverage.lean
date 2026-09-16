import SixVertexUnfolding.Geometry.UniversalVertexOrder

/-! The cyclic list exhausts all original faces incident to the
universal vertex. Thus the five sectors describe its whole local surface. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set

/-- The five cyclically listed triangular faces are all distinct. -/
theorem five_cyclic_faces_injective (P : ConvexPolyhedron) (source : P.Vertex)
    (order : Fin 5 ≃ {v : P.Vertex // v ≠ source}) (faces : Fin 5 → P.Face)
    (vertices : ∀ i : Fin 5, (faces i).val ∩ (P.vertices : Set Space) =
      {(source : Space), ((order i).val : Space), ((order (i + 1)).val : Space)}) :
    Function.Injective faces := by
  have membership (i k : Fin 5) :
      ((order k).val : Space) ∈ (faces i).val ∩ (P.vertices : Set Space) ↔ k = i ∨ k = i + 1 := by
    rw [vertices]
    simp only [mem_insert_iff, mem_singleton_iff, Subtype.coe_inj,
      (order k).property, false_or, order.injective.eq_iff]
  intro i j same
  have pairs : ({i, i + 1} : Finset (Fin 5)) = {j, j + 1} := by
    ext k
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rw [← membership i k, ← membership j k, same]
  exact (by decide : Function.Injective (fun i : Fin 5 => ({i, i + 1} : Finset (Fin 5)))) pairs

/-- No incident face is missing from the five cyclic sectors. -/
theorem universal_vertex_fan_covers (P : ConvexPolyhedron)
    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4)
    (source : P.Vertex) (universal : ∀ v : P.Vertex, v ≠ source → P.edgeGraph.Adj source v)
    (order : Fin 5 ≃ {v : P.Vertex // v ≠ source}) (faces : Fin 5 → P.Face)
    (vertices : ∀ i : Fin 5, (faces i).val ∩ (P.vertices : Set Space) =
      {(source : Space), ((order i).val : Space), ((order (i + 1)).val : Space)}) :
    ∀ F : P.Face, (source : Space) ∈ F.val ↔ F ∈ range faces := by
  have consecutive (i : Fin 5) : (P.vertexLink source).Adj (order i) (order (i + 1)) := by
    refine ⟨fun same => ?_, faces i, ?_, ?_, ?_⟩
    · have impossible := order.injective same
      exact (by decide : ∀ i : Fin 5, i ≠ i + 1) i impossible
    all_goals
      apply (show (faces i).val ∩ (P.vertices : Set Space) ⊆ (faces i).val from inter_subset_left)
      rw [vertices]
      simp
  have two (v : {v : P.Vertex // v ≠ source}) : ((P.vertexLink source).neighborSet v).ncard = 2 := by
    obtain ⟨c, d, distinct, neighbors⟩ := P.universal_vertex_link_neighbors small_faces source universal v
    rw [neighbors, Set.ncard_pair distinct]
  intro F
  constructor
  · intro sourceF
    have triangle := P.universal_vertex_facets_triangular small_faces source universal F sourceF
    have another : ¬ F.val ∩ (P.vertices : Set Space) ⊆ {(source : Space)} := by
      intro included
      have bound := Set.ncard_le_ncard included (finite_singleton _)
      rw [triangle, Set.ncard_singleton] at bound
      omega
    obtain ⟨a, aF, nonsource⟩ := Set.not_subset.mp another
    let A : {v : P.Vertex // v ≠ source} :=
      ⟨⟨a, aF.2⟩, fun same => nonsource (congrArg Subtype.val same)⟩
    obtain ⟨b, bs, ba, face_vertices⟩ := F.exists_third_vertex triangle source A.val A.property.symm sourceF aF.1
    let B : {v : P.Vertex // v ≠ source} := ⟨b, bs⟩
    have bF : (b : Space) ∈ F.val := by
      have member : (b : Space) ∈ F.val ∩ (P.vertices : Set Space) := by rw [face_vertices]; simp
      exact member.1
    have adjacent : (P.vertexLink source).Adj A B :=
      ⟨fun same => ba (congrArg Subtype.val same).symm, F, sourceF, aF.1, bF⟩
    let i := order.symm A
    have at_i : order i = A := order.apply_symm_apply A
    have neighbor : B ∈ (P.vertexLink source).neighborSet (order i) := by rw [at_i]; exact adjacent
    rw [five_cycle_neighbors (P.vertexLink source) two order consecutive i] at neighbor
    rcases neighbor with previous | next
    · refine ⟨i - 1, ?_⟩
      apply (faces (i - 1)).eq_of_same_vertices F
      rw [vertices, sub_add_cancel, at_i, face_vertices, ← previous]
      ext x
      simp only [mem_insert_iff, mem_singleton_iff]
      tauto
    · refine ⟨i, ?_⟩
      apply (faces i).eq_of_same_vertices F
      rw [vertices, at_i, face_vertices, ← next]
  · rintro ⟨i, rfl⟩
    have member : (source : Space) ∈ (faces i).val ∩ (P.vertices : Set Space) := by rw [vertices]; simp
    exact member.1

/-- A universal vertex in this six-vertex family has exactly five incident original faces. -/
theorem universal_vertex_incident_face_count (P : ConvexPolyhedron) (size : P.vertices.card = 6)
    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4)
    (source : P.Vertex) (universal : ∀ v : P.Vertex, v ≠ source → P.edgeGraph.Adj source v) :
    Nat.card {F : P.Face // (source : Space) ∈ F.val} = 5 := by
  obtain ⟨order, faces, vertices⟩ := P.universal_vertex_face_order size small_faces source universal
  have covers := P.universal_vertex_fan_covers small_faces source universal order faces vertices
  let index : Fin 5 → {F : P.Face // (source : Space) ∈ F.val} :=
    fun i => ⟨faces i, (covers (faces i)).mpr (mem_range_self i)⟩
  have injective : Function.Injective index := by
    intro i j same
    exact P.five_cyclic_faces_injective source order faces vertices (congrArg Subtype.val same)
  have surjective : Function.Surjective index := by
    intro F
    obtain ⟨i, at_face⟩ := (covers F.val).mp F.property
    exact ⟨i, Subtype.ext at_face⟩
  simpa using (Nat.card_congr (Equiv.ofBijective index ⟨injective, surjective⟩)).symm

end SixVertexUnfolding.ConvexPolyhedron
