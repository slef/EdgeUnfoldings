import SixVertexUnfolding.Definitions

/-! The union of two disjoint continuous graphs is a product with two
points. This supplies a concrete covering chart for the shortest-route family. -/

namespace SixVertexUnfolding

open Set

def twoGraphs {X Y : Type*} (f g : X → Y) : Set (X × Y) :=
  {p | p.2 = f p.1 ∨ p.2 = g p.1}

/-- Two continuous pointwise-distinct branches give an actual two-sheet product homeomorphism. -/
noncomputable def twoGraphsHomeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] (f g : X → Y) (hf : Continuous f) (hg : Continuous g)
    (different : ∀ x, f x ≠ g x) : twoGraphs f g ≃ₜ X × Bool := by
  classical
  let first : Set (twoGraphs f g) := {e | e.val.2 = f e.val.1}
  have first_closed : IsClosed first := isClosed_eq continuous_subtype_val.snd (hf.comp continuous_subtype_val.fst)
  have complement : firstᶜ = {e : twoGraphs f g | e.val.2 = g e.val.1} := by
    ext e
    constructor
    · exact fun outside => e.property.resolve_left outside
    · intro second first
      exact different e.val.1 (first.symm.trans second)
  have first_open : IsOpen first := by
    have closed : IsClosed firstᶜ := by
      rw [complement]
      exact isClosed_eq continuous_subtype_val.snd (hg.comp continuous_subtype_val.fst)
    simpa only [compl_compl] using closed.isOpen_compl
  let label (e : twoGraphs f g) : Bool := if e ∈ first then true else false
  have continuous_label : Continuous label := by
    rw [continuous_bool_rng true]
    convert (show IsClopen first from ⟨first_closed, first_open⟩) using 1
    ext e
    simp [label]
  let unlabel (p : X × Bool) : twoGraphs f g :=
    ⟨(p.1, if p.2 then f p.1 else g p.1), by cases p.2 <;> simp [twoGraphs]⟩
  have continuous_unlabel : Continuous unlabel := by
    apply Continuous.subtype_mk
    apply continuous_fst.prodMk
    apply continuous_prod_of_discrete_right.mpr
    intro flag
    cases flag
    · simpa using hg
    · simpa using hf
  exact {
    toFun := fun e => (e.val.1, label e)
    invFun := unlabel
    left_inv := by
      intro e
      apply Subtype.ext
      apply Prod.ext
      · rfl
      by_cases member : e ∈ first
      · simpa only [unlabel, label, if_pos member, Bool.true_eq_false, ↓reduceIte] using member.symm
      · simpa only [unlabel, label, if_neg member, Bool.false_eq_true, ↓reduceIte] using
          (e.property.resolve_left member).symm
    right_inv := by
      rintro ⟨x, flag⟩
      apply Prod.ext
      · rfl
      cases flag <;> simp [unlabel, label, first, (different x).symm]
    continuous_toFun := continuous_subtype_val.fst.prodMk continuous_label
    continuous_invFun := continuous_unlabel }

/-- The product chart leaves the base coordinate unchanged. -/
theorem twoGraphsHomeomorph_fst {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    (f g : X → Y) (hf : Continuous f) (hg : Continuous g) (different : ∀ x, f x ≠ g x)
    (e : twoGraphs f g) : (twoGraphsHomeomorph f g hf hg different e).1 = e.val.1 := rfl

end SixVertexUnfolding
