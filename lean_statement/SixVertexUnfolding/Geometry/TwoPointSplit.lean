import SixVertexUnfolding.Definitions

/-! A two-point set covered by two disjoint regions, each containing at
most one point, has exactly one point in each region. -/

namespace SixVertexUnfolding

open Set

theorem two_point_split {X : Type*} (S U V : Set X) (two : S.ncard = 2)
    (covered : S ⊆ U ∪ V) (apart : Disjoint U V)
    (first_unique : (S ∩ U).Subsingleton) (second_unique : (S ∩ V).Subsingleton) :
    ∃ f ∈ S ∩ U, ∃ g ∈ S ∩ V, f ≠ g ∧ S = {f, g} := by
  obtain ⟨x, y, distinct, pair⟩ := ncard_eq_two.mp two
  have xS : x ∈ S := by rw [pair]; simp
  have yS : y ∈ S := by rw [pair]; simp
  have first_exists : (S ∩ U).Nonempty := by
    by_contra none
    have xV := (covered xS).resolve_left (fun hx => none ⟨x, xS, hx⟩)
    have yV := (covered yS).resolve_left (fun hy => none ⟨y, yS, hy⟩)
    exact distinct (second_unique ⟨xS, xV⟩ ⟨yS, yV⟩)
  have second_exists : (S ∩ V).Nonempty := by
    by_contra none
    have xU := (covered xS).resolve_right (fun hx => none ⟨x, xS, hx⟩)
    have yU := (covered yS).resolve_right (fun hy => none ⟨y, yS, hy⟩)
    exact distinct (first_unique ⟨xS, xU⟩ ⟨yS, yU⟩)
  obtain ⟨f, hf⟩ := first_exists
  obtain ⟨g, hg⟩ := second_exists
  refine ⟨f, hf, g, hg, fun same => disjoint_left.mp apart hf.2 (same ▸ hg.2), ?_⟩
  ext z
  constructor
  · intro hz
    rcases covered hz with first | second
    · exact Or.inl (first_unique ⟨hz, first⟩ hf)
    · exact Or.inr (second_unique ⟨hz, second⟩ hg)
  · rintro (rfl | rfl)
    · exact hf.1
    · exact hg.1

end SixVertexUnfolding
