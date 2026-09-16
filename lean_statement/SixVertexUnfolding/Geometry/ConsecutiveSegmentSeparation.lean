import SixVertexUnfolding.Geometry.SegmentArrangementGraph

/-! Consecutive segments on one line cannot overlap in their interiors
unless they have the same unordered endpoint pair. -/

namespace SixVertexUnfolding

open Set

theorem intervals_equal_of_overlap_no_endpoints {l r u v t : ℝ}
    (first : t ∈ Ioo l r) (second : t ∈ Ioo u v)
    (l_out : l ∉ Ioo u v) (r_out : r ∉ Ioo u v)
    (u_out : u ∉ Ioo l r) (v_out : v ∉ Ioo l r) : l = u ∧ r = v := by
  have lu : l ≤ u := le_of_not_gt (fun ul => l_out ⟨ul, first.1.trans second.2⟩)
  have ul : u ≤ l := le_of_not_gt (fun lu => u_out ⟨lu, second.1.trans first.2⟩)
  have rv : r ≤ v := le_of_not_gt (fun vr => v_out ⟨first.1.trans second.2, vr⟩)
  have vr : v ≤ r := le_of_not_gt (fun rv => r_out ⟨second.1.trans first.2, rv⟩)
  exact ⟨le_antisymm lu ul, le_antisymm rv vr⟩

/-- Two collinear segments with no subdivision vertex in their interiors have no partial overlap. -/
theorem consecutive_collinear_segments (V : Set Space) {a b c d x : Space}
    (aV : a ∈ V) (bV : b ∈ V) (cV : c ∈ V) (dV : d ∈ V)
    (ab : a ≠ b) (cd : c ≠ d)
    (c_line : c ∈ affineSpan ℝ ({a, b} : Set Space)) (d_line : d ∈ affineSpan ℝ ({a, b} : Set Space))
    (first_empty : Disjoint (openSegment ℝ a b) V) (second_empty : Disjoint (openSegment ℝ c d) V)
    (first : x ∈ openSegment ℝ a b) (second : x ∈ openSegment ℝ c d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  let curve : ℝ →ᵃ[ℝ] Space := AffineMap.lineMap a b
  have injective : Function.Injective curve := AffineMap.lineMap_injective ℝ ab
  obtain ⟨u, cu⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp c_line
  obtain ⟨v, cv⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp d_line
  have different : u ≠ v := by intro same; exact cd (cu.symm.trans (same ▸ cv))
  rw [openSegment_eq_image_lineMap] at first
  obtain ⟨t, ht, ct⟩ := first
  have image_second : openSegment ℝ c d = curve '' Ioo (min u v) (max u v) := by
    rw [← openSegment_eq_Ioo' different, image_openSegment]
    rw [show curve u = c from cu, show curve v = d from cv]
  have middle : t ∈ Ioo (min u v) (max u v) := by
    rw [image_second] at second
    obtain ⟨s, hs, cs⟩ := second
    have same : s = t := injective (cs.trans ct.symm)
    exact same ▸ hs
  have outside_first (s : ℝ) (member : curve s ∈ V) : s ∉ Ioo (0 : ℝ) 1 := by
    intro hs
    apply disjoint_left.mp first_empty _ member
    rw [openSegment_eq_image_lineMap]
    exact ⟨s, hs, rfl⟩
  have u_out := outside_first u (by rw [show curve u = c from cu]; exact cV)
  have v_out := outside_first v (by rw [show curve v = d from cv]; exact dV)
  have outside_second (s : ℝ) (member : curve s ∈ V) : s ∉ Ioo (min u v) (max u v) := by
    intro hs
    apply disjoint_left.mp second_empty _ member
    rw [image_second]
    exact ⟨s, hs, rfl⟩
  have zero_out := outside_second 0 (by simpa only [curve, AffineMap.lineMap_apply_zero] using aV)
  have one_out := outside_second 1 (by simpa only [curve, AffineMap.lineMap_apply_one] using bV)
  have min_out : min u v ∉ Ioo (0 : ℝ) 1 := by
    rcases le_total u v with h | h
    · rwa [min_eq_left h]
    · rwa [min_eq_right h]
  have max_out : max u v ∉ Ioo (0 : ℝ) 1 := by
    rcases le_total u v with h | h
    · rwa [max_eq_right h]
    · rwa [max_eq_left h]
  obtain ⟨low, high⟩ := intervals_equal_of_overlap_no_endpoints ht middle zero_out one_out min_out max_out
  rcases le_total u v with h | h
  · have u_zero : u = 0 := by simpa only [min_eq_left h] using low.symm
    have v_one : v = 1 := by simpa only [max_eq_right h] using high.symm
    exact Or.inl ⟨by simpa only [u_zero, AffineMap.lineMap_apply_zero] using cu,
      by simpa only [v_one, AffineMap.lineMap_apply_one] using cv⟩
  · have v_zero : v = 0 := by simpa only [min_eq_right h] using low.symm
    have u_one : u = 1 := by simpa only [max_eq_left h] using high.symm
    exact Or.inr ⟨by simpa only [v_zero, AffineMap.lineMap_apply_zero] using cv,
      by simpa only [u_one, AffineMap.lineMap_apply_one] using cu⟩

end SixVertexUnfolding
