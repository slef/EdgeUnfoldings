import Mathlib

/-!
The curvature part of the paired-pole selector (PAIRED_POLE_RULE.md).
These are real inequalities. A later geometric bridge must supply positivity,
the total curvature, and the upper bound at the source from a convex polyhedron.
-/

namespace SixVertexUnfolding.Curvature

open Real

/-- Four equator vertices always have a maximum-curvature choice, including ties. -/
theorem equator_has_maximum (equator : Fin 4 → ℝ) :
    ∃ c, ∀ i, equator i ≤ equator c := by
  obtain ⟨c, _, maximal⟩ := Finset.univ.exists_max_image equator Finset.univ_nonempty
  exact ⟨c, fun i => maximal i (Finset.mem_univ i)⟩

/-- A maximum on the equator supplies a strictly stronger slit threshold. -/
theorem equator_maximum_slit_threshold
    {source fan : ℝ} {equator : Fin 4 → ℝ} {c : Fin 4}
    (total : source + fan + ∑ i, equator i = 4 * π)
    (source_lt : source < 2 * π) (fan_pos : 0 < fan)
    (maximal : ∀ i, equator i ≤ equator c) :
    π < 2 * equator c + fan := by
  have equator_bound : ∑ i, equator i ≤ 4 * equator c := by
    calc
      ∑ i, equator i ≤ ∑ _i : Fin 4, equator c :=
        Finset.sum_le_sum (fun i _ => maximal i)
      _ = 4 * equator c := by simp
  linarith

/-- Source order gives exactly the alternative needed by the half-fan lemma. -/
theorem half_fan_alternative {source fan : ℝ} (source_order : fan ≤ source) :
    π ≤ source ∨ fan ≤ π := by
  by_cases high : π ≤ source
  · exact Or.inl high
  · exact Or.inr (by linarith)

/-- In the low-source branch, every slit-adjacent triple exceeds pi. -/
theorem equator_maximum_lower_face_sums
    {source fan a b c d : ℝ}
    (total : source + fan + a + b + c + d = 4 * π)
    (source_low : source < π)
    (fan_pos : 0 < fan) (a_pos : 0 < a) (b_pos : 0 < b) (d_pos : 0 < d)
    (a_le : a ≤ c) (b_le : b ≤ c) (d_le : d ≤ c) :
    π < fan + c + a ∧ π < fan + c + b ∧ π < fan + c + d := by
  by_cases slit_high : π ≤ c
  · exact ⟨by linarith, by linarith, by linarith⟩
  · exact ⟨by linarith, by linarith, by linarith⟩

/-- A low-curvature six-vertex solid has every three-vertex sum at least pi. -/
theorem triple_lower_bound
    {a b c d e f : ℝ} (total : a + b + c + d + e + f = 4 * π)
    (d_low : d ≤ π) (e_low : e ≤ π) (f_low : f ≤ π) :
    π ≤ a + b + c := by
  linarith

/-- The chosen equator maximum satisfies the scalar part of criterion (P).
This asserts a choice and its bounds, not yet an unfolding of a polyhedron. -/
theorem exists_slit_satisfying_criterion
    {source fan : ℝ} {equator : Fin 4 → ℝ}
    (total : source + fan + ∑ i, equator i = 4 * π)
    (source_lt : source < 2 * π) (fan_pos : 0 < fan)
    (equator_pos : ∀ i, 0 < equator i) :
    ∃ c : Fin 4,
      (∀ i, equator i ≤ equator c) ∧
      π < 2 * equator c + fan ∧
      (π ≤ source ∨ ∀ i, π < fan + equator c + equator i) := by
  obtain ⟨c, maximal⟩ := equator_has_maximum equator
  have threshold := equator_maximum_slit_threshold total source_lt fan_pos maximal
  refine ⟨c, maximal, threshold, ?_⟩
  by_cases source_high : π ≤ source
  · exact Or.inl source_high
  right
  intro i
  by_cases slit_high : π ≤ equator c
  · linarith [equator_pos i]
  by_cases same : i = c
  · subst i
    linarith
  -- Removing the slit and this vertex leaves exactly two equator vertices.
  let others := (Finset.univ.erase c).erase i
  have other_bound : ∑ j ∈ others, equator j ≤ 2 * π := by
    calc
      ∑ j ∈ others, equator j ≤ ∑ _j ∈ others, π :=
        Finset.sum_le_sum (fun j _ => by linarith [maximal j])
      _ = 2 * π := by simp [others, Finset.card_erase_of_mem, same]
  have remove_slit := Finset.sum_erase_add Finset.univ equator (Finset.mem_univ c)
  have remove_vertex := Finset.sum_erase_add (Finset.univ.erase c) equator
    (by simp [same] : i ∈ Finset.univ.erase c)
  change (∑ j ∈ others, equator j) + equator i =
    ∑ j ∈ Finset.univ.erase c, equator j at remove_vertex
  linarith

end SixVertexUnfolding.Curvature
