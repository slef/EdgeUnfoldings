import SixVertexUnfolding.Geometry.CutRayCoordinates

/-! Exact intersections of closed shortest rays to the cut set.
Distinct rays can meet only at the source or at a common terminal point. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include graph small_faces in
/-- A common point is the source, a common endpoint, or belongs to two identical rays. -/
theorem closed_cut_rays_intersection (a b c : frontier P.body)
    (cut_b : b ∈ P.cutSet a) (cut_c : c ∈ P.cutSet a)
    (f g : P.BoundaryCurve) (hf : f ∈ P.geodesicFiber a b) (hg : g ∈ P.geodesicFiber a c)
    (x : frontier P.body) :
    x ∈ range f ∩ range g ↔ x = a ∨ (b = c ∧ x = b) ∨ (f = g ∧ x ∈ range f) := by
  have f0 : f 0 = a := congrArg Prod.fst hf.2
  have f1 : f 1 = b := congrArg Prod.snd hf.2
  have g0 : g 0 = a := congrArg Prod.fst hg.2
  have g1 : g 1 = c := congrArg Prod.snd hg.2
  constructor
  · rintro ⟨⟨s, rfl⟩, ⟨t, meet⟩⟩
    by_cases zero : s = 0
    · exact Or.inl (zero ▸ f0)
    have positive : 0 < s := lt_of_le_of_ne s.property.1 (Ne.symm zero)
    by_cases last : s = 1
    · by_cases other_last : t = 1
      · right; left
        refine ⟨?_, last ▸ f1⟩
        simpa only [last, other_last, f1, g1] using meet.symm
      have other_zero : t ≠ 0 := by
        intro ht
        rw [ht, g0, last, f1] at meet
        exact P.source_not_cutSet a (meet.symm ▸ cut_b)
      have result := graph.cut_rays_meeting small_faces a c b cut_c cut_b g f hg hf t s
        (lt_of_le_of_ne t.property.1 (Ne.symm other_zero))
        (lt_of_le_of_ne t.property.2 other_last) meet
      exact Or.inr (Or.inr ⟨result.2.2.symm, mem_range_self s⟩)
    · have result := graph.cut_rays_meeting small_faces a b c cut_b cut_c f g hf hg s t
        positive (lt_of_le_of_ne s.property.2 last) meet.symm
      exact Or.inr (Or.inr ⟨result.2.2, mem_range_self s⟩)
  · rintro (rfl | ⟨same, rfl⟩ | ⟨rfl, inside⟩)
    · exact ⟨⟨0, f0⟩, ⟨0, g0⟩⟩
    · exact ⟨⟨1, f1⟩, ⟨1, g1.trans same.symm⟩⟩
    · exact ⟨inside, inside⟩

include graph small_faces in
/-- Rays with different terminal cut points intersect exactly at the source. -/
theorem closed_cut_rays_intersection_of_distinct_targets (a b c : frontier P.body)
    (cut_b : b ∈ P.cutSet a) (cut_c : c ∈ P.cutSet a) (different : b ≠ c)
    (f g : P.BoundaryCurve) (hf : f ∈ P.geodesicFiber a b) (hg : g ∈ P.geodesicFiber a c) :
    range f ∩ range g = {a} := by
  have distinct_routes : f ≠ g := by
    intro same
    apply different
    exact (congrArg Prod.snd hf.2).symm.trans
      ((congrArg (fun route : P.BoundaryCurve => route 1) same).trans (congrArg Prod.snd hg.2))
  ext x
  rw [graph.closed_cut_rays_intersection small_faces a b c cut_b cut_c f g hf hg]
  simp only [different, distinct_routes, false_and, or_false, mem_singleton_iff]

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
