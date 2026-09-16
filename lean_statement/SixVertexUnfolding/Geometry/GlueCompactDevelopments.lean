import SixVertexUnfolding.Geometry.EqualFibersHomeomorph
import Mathlib.Topology.Constructions.SumProd

/-! Glue two compact developments when their coordinates make exactly
the same identifications along the common boundary. -/

namespace SixVertexUnfolding

open Set

/-- Two compact pieces with matching surface and planar identifications give a development of their union. -/
theorem glue_compact_developments {X Y : Type*} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace Y] [T2Space Y] (A B : Set X) (C D : Set Y)
    (compactA : IsCompact A) (compactB : IsCompact B) (H : A ≃ₜ C) (K : B ≃ₜ D)
    (cross : ∀ x : A, ∀ y : B, (x : X) = (y : X) ↔ (H x : Y) = (K y : Y)) :
    ∃ joined : (A ∪ B : Set X) ≃ₜ (C ∪ D : Set Y),
      (∀ x : A, (joined ⟨x, Or.inl x.property⟩ : Y) = (H x : Y)) ∧
      (∀ y : B, (joined ⟨y, Or.inr y.property⟩ : Y) = (K y : Y)) := by
  letI : CompactSpace A := isCompact_iff_compactSpace.mp compactA
  letI : CompactSpace B := isCompact_iff_compactSpace.mp compactB
  let surface : C(A ⊕ B, X) := ⟨Sum.elim Subtype.val Subtype.val,
    continuous_subtype_val.sumElim continuous_subtype_val⟩
  let planar : C(A ⊕ B, Y) := ⟨Sum.elim (fun x => (H x : Y)) (fun y => (K y : Y)),
    (continuous_subtype_val.comp H.continuous).sumElim (continuous_subtype_val.comp K.continuous)⟩
  have same_fibers : ∀ x y, surface x = surface y ↔ planar x = planar y := by
    rintro (x | x) (y | y)
    · change (x : X) = (y : X) ↔ (H x : Y) = (H y : Y)
      constructor
      · intro same
        rw [Subtype.ext same]
      · intro same
        exact congrArg Subtype.val (H.injective (Subtype.ext same))
    · exact cross x y
    · exact eq_comm.trans ((cross y x).trans eq_comm)
    · change (x : X) = (y : X) ↔ (K x : Y) = (K y : Y)
      constructor
      · intro same
        rw [Subtype.ext same]
      · intro same
        exact congrArg Subtype.val (K.injective (Subtype.ext same))
  obtain ⟨joined, agrees⟩ := equal_fibers_homeomorph surface planar same_fibers
  have surface_range : range surface = A ∪ B := by
    ext x
    constructor
    · rintro ⟨y | y, rfl⟩
      · exact Or.inl y.property
      · exact Or.inr y.property
    · rintro (inside | inside)
      · exact ⟨Sum.inl ⟨x, inside⟩, rfl⟩
      · exact ⟨Sum.inr ⟨x, inside⟩, rfl⟩
  have planar_range : range planar = C ∪ D := by
    ext y
    constructor
    · rintro ⟨x | x, rfl⟩
      · exact Or.inl (H x).property
      · exact Or.inr (K x).property
    · rintro (inside | inside)
      · exact ⟨Sum.inl (H.symm ⟨y, inside⟩), congrArg Subtype.val (H.apply_symm_apply _)⟩
      · exact ⟨Sum.inr (K.symm ⟨y, inside⟩), congrArg Subtype.val (K.apply_symm_apply _)⟩
  refine ⟨((Homeomorph.setCongr surface_range).symm.trans joined).trans
    (Homeomorph.setCongr planar_range), ?_, ?_⟩
  · intro x
    exact congrArg Subtype.val (agrees (Sum.inl x))
  · intro y
    exact congrArg Subtype.val (agrees (Sum.inr y))

end SixVertexUnfolding
