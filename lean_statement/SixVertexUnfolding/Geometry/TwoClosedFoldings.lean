import SixVertexUnfolding.Geometry.ClosedCoverMaps
import SixVertexUnfolding.Geometry.FiniteRigidPieces

/-! Two compatible continuous foldings on closed planar regions
paste into one folding with the same finite rigid formulas. -/

namespace SixVertexUnfolding

open Set

theorem glue_two_closed_foldings {Y : Type*} [TopologicalSpace Y]
    (A B : Set Plane) (closedA : IsClosed A) (closedB : IsClosed B)
    (f : C(A, Y)) (g : C(B, Y))
    (compatible : ∀ x (hx : x ∈ A) (hy : x ∈ B), f ⟨x, hx⟩ = g ⟨x, hy⟩) :
    ∃ glued : C((A ∪ B : Set Plane), Y),
      (∀ x : A, glued ⟨x, Or.inl x.property⟩ = f x) ∧
      (∀ x : B, glued ⟨x, Or.inr x.property⟩ = g x) := by
  let pieces : Bool → Set Plane | false => A | true => B
  let maps : ∀ side, C(pieces side, Y) | false => f | true => g
  have closed : ∀ side, IsClosed (pieces side) := by intro side; cases side <;> assumption
  have matching : ∀ i j (x : Plane) (hi : x ∈ pieces i) (hj : x ∈ pieces j),
      maps i ⟨x, hi⟩ = maps j ⟨x, hj⟩ := by
    intro i j x hi hj
    cases i <;> cases j
    · rfl
    · exact compatible x hi hj
    · exact (compatible x hj hi).symm
    · rfl
  obtain ⟨glued, agrees⟩ := glue_finite_closed_maps pieces closed maps matching
  have cover : (⋃ side, pieces side) = A ∪ B := by
    ext x
    simp only [mem_iUnion, mem_union]
    constructor
    · rintro ⟨side, member⟩
      cases side
      · exact Or.inl member
      · exact Or.inr member
    · rintro (member | member)
      · exact ⟨false, member⟩
      · exact ⟨true, member⟩
  let fold : C((A ∪ B : Set Plane), Y) :=
    ⟨fun x => glued ((Homeomorph.setCongr cover).symm x),
      glued.continuous.comp (Homeomorph.setCongr cover).symm.continuous⟩
  exact ⟨fold, agrees false, agrees true⟩

/-- The pasted map retains the union of the two finite sets of rigid formulas. -/
theorem finite_rigid_pieces_union (A B : Set Plane) (fold : (A ∪ B : Set Plane) → Space)
    (left : HasFiniteRigidPieces A (fun x => fold ⟨x, Or.inl x.property⟩))
    (right : HasFiniteRigidPieces B (fun x => fold ⟨x, Or.inr x.property⟩)) :
    HasFiniteRigidPieces (A ∪ B) fold := by
  obtain ⟨mapsA, finiteA, rigidA, selectedA⟩ := left
  obtain ⟨mapsB, finiteB, rigidB, selectedB⟩ := right
  refine ⟨mapsA ∪ mapsB, finiteA.union finiteB, ?_, ?_⟩
  · intro f hf
    rcases hf with ha | hb
    · exact rigidA f ha
    · exact rigidB f hb
  · intro x
    rcases x.property with ha | hb
    · obtain ⟨f, hf, agrees⟩ := selectedA ⟨x, ha⟩
      exact ⟨f, Or.inl hf, agrees⟩
    · obtain ⟨f, hf, agrees⟩ := selectedB ⟨x, hb⟩
      exact ⟨f, Or.inr hf, agrees⟩

end SixVertexUnfolding
