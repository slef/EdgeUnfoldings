import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Separation.Basic

/-! On a connected parameter domain, a continuous choice of one of two
distinct continuous branches cannot switch labels. -/

namespace SixVertexUnfolding

open Set

/-- A continuous two-branch selection makes one choice on the entire domain. -/
theorem continuous_two_branch_choice {X Y : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] [TopologicalSpace Y] [T2Space Y]
    (f g h : X → Y) (cf : Continuous f) (cg : Continuous g) (ch : Continuous h)
    (distinct : ∀ x, g x ≠ h x) (selected : ∀ x, f x = g x ∨ f x = h x) :
    f = g ∨ f = h := by
  let first := {x | f x = g x}
  let second := {x | f x = h x}
  have covers : (univ : Set X) ⊆ first ∪ second := fun x _ => selected x
  have disjoint : (univ : Set X) ∩ (first ∩ second) = ∅ := by
    apply subset_empty_iff.mp
    rintro x ⟨_, left, right⟩
    exact distinct x (left.symm.trans right)
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp isPreconnected_univ)
      first second (isClosed_eq cf cg) (isClosed_eq cf ch) covers disjoint with all_first | all_second
  · exact Or.inl (funext (fun x => all_first (mem_univ x)))
  · exact Or.inr (funext (fun x => all_second (mem_univ x)))

end SixVertexUnfolding
