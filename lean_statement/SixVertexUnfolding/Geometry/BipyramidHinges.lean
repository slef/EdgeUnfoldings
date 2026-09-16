import SixVertexUnfolding.Geometry.BipyramidFaceIndex

/-! Original hinge edges within each three-triangle cap and across the equator. -/

namespace SixVertexUnfolding.ConvexPolyhedron.BipyramidVertices

variable {P : ConvexPolyhedron} (B : BipyramidVertices P)

/-- Distinct face indices leave exactly one common equator index. -/
theorem remaining_equator_index (i j : Fin 3) (different : i ≠ j) :
    ∃ k : Fin 3, k ≠ i ∧ k ≠ j ∧ ∀ l : Fin 3, (l ≠ i ∧ l ≠ j) ↔ l = k := by
  have exists_third : ∃ k : Fin 3, k ≠ i ∧ k ≠ j := by
    fin_cases i <;> fin_cases j <;> first
      | exact False.elim (different rfl)
      | exact ⟨0, by decide, by decide⟩
      | exact ⟨1, by decide, by decide⟩
      | exact ⟨2, by decide, by decide⟩
  obtain ⟨k, ki, kj⟩ := exists_third
  exact ⟨k, ki, kj, fun l => by omega⟩

/-- Two different triangles on the same cap share a pole-to-equator original edge. -/
theorem same_cap_shareEdge
    (triangles : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3)
    (upper : Bool) (i j : Fin 3) (different : i ≠ j) :
    P.ShareEdge (B.face triangles upper i) (B.face triangles upper j) := by
  obtain ⟨k, ki, kj, remaining⟩ := remaining_equator_index i j different
  have common :
      (((B.face triangles upper i).val ∩ (B.face triangles upper j).val) ∩ (P.vertices : Set Space)) =
        {(B.poleVertex upper : Space), (B.equatorVertex k : Space)} := by
    ext x
    constructor
    · rintro ⟨⟨xi, xj⟩, vertex⟩
      let v : P.Vertex := ⟨x, vertex⟩
      rcases B.vertex_cases_from_pole upper v with pole | opposite | ⟨l, equal⟩
      · exact Or.inl (congrArg Subtype.val pole)
      · have bad : (B.poleVertex (!upper) : Space) ∈ (B.face triangles upper i).val :=
          (congrArg Subtype.val opposite) ▸ xi
        exact False.elim (B.opposite_pole_not_mem_face triangles upper i bad)
      · have li : l ≠ i := (B.equator_mem_face triangles upper i l).mp ((congrArg Subtype.val equal) ▸ xi)
        have lj : l ≠ j := (B.equator_mem_face triangles upper j l).mp ((congrArg Subtype.val equal) ▸ xj)
        exact Or.inr ((congrArg Subtype.val equal).trans
          (congrArg (fun m => (B.equatorVertex m : Space)) ((remaining l).mp ⟨li, lj⟩)))
    · rintro (rfl | rfl)
      · exact ⟨⟨B.pole_mem_face triangles upper i, B.pole_mem_face triangles upper j⟩,
          (B.poleVertex upper).property⟩
      · exact ⟨⟨(B.equator_mem_face triangles upper i k).mpr ki,
          (B.equator_mem_face triangles upper j k).mpr kj⟩, (B.equatorVertex k).property⟩
  change affineDimension ((B.face triangles upper i).val ∩ (B.face triangles upper j).val) = 1
  rw [(B.face triangles upper i).intersection_eq_convexHull_vertices (B.face triangles upper j),
    common, affineDimension_convexHull]
  exact affineDimension_pair (fun same => B.pole_ne_equator upper k (Subtype.ext same))

/-- Corresponding upper and lower triangles share an original equator edge. -/
theorem across_equator_shareEdge
    (triangles : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3)
    (upper : Bool) (missing : Fin 3) :
    P.ShareEdge (B.face triangles upper missing) (B.face triangles (!upper) missing) := by
  obtain ⟨i, j, different, pair⟩ := equator_complement_pair missing
  have remaining (k : Fin 3) : k ≠ missing ↔ k = i ∨ k = j := by
    exact Set.ext_iff.mp pair k
  have im := (remaining i).mpr (Or.inl rfl)
  have jm := (remaining j).mpr (Or.inr rfl)
  have common :
      (((B.face triangles upper missing).val ∩ (B.face triangles (!upper) missing).val) ∩
        (P.vertices : Set Space)) = {(B.equatorVertex i : Space), (B.equatorVertex j : Space)} := by
    ext x
    constructor
    · rintro ⟨⟨left, right⟩, vertex⟩
      let v : P.Vertex := ⟨x, vertex⟩
      rcases B.vertex_cases_from_pole upper v with pole | opposite | ⟨k, equal⟩
      · have bad : (B.poleVertex upper : Space) ∈ (B.face triangles (!upper) missing).val :=
          (congrArg Subtype.val pole) ▸ right
        have excluded : (B.poleVertex upper : Space) ∉ (B.face triangles (!upper) missing).val := by
          simpa only [Bool.not_not] using B.opposite_pole_not_mem_face triangles (!upper) missing
        exact False.elim (excluded bad)
      · have bad : (B.poleVertex (!upper) : Space) ∈ (B.face triangles upper missing).val :=
          (congrArg Subtype.val opposite) ▸ left
        exact False.elim (B.opposite_pole_not_mem_face triangles upper missing bad)
      · have km := (B.equator_mem_face triangles upper missing k).mp
          ((congrArg Subtype.val equal) ▸ left)
        rcases (remaining k).mp km with ki | kj
        · exact Or.inl ((congrArg Subtype.val equal).trans (congrArg (fun l => (B.equatorVertex l : Space)) ki))
        · exact Or.inr ((congrArg Subtype.val equal).trans (congrArg (fun l => (B.equatorVertex l : Space)) kj))
    · rintro (rfl | rfl)
      · exact ⟨⟨(B.equator_mem_face triangles upper missing i).mpr im,
          (B.equator_mem_face triangles (!upper) missing i).mpr im⟩, (B.equatorVertex i).property⟩
      · exact ⟨⟨(B.equator_mem_face triangles upper missing j).mpr jm,
          (B.equator_mem_face triangles (!upper) missing j).mpr jm⟩, (B.equatorVertex j).property⟩
  change affineDimension ((B.face triangles upper missing).val ∩ (B.face triangles (!upper) missing).val) = 1
  rw [(B.face triangles upper missing).intersection_eq_convexHull_vertices (B.face triangles (!upper) missing),
    common, affineDimension_convexHull]
  exact affineDimension_pair (fun same => different (B.equator_injective (Subtype.ext same)))

end SixVertexUnfolding.ConvexPolyhedron.BipyramidVertices
