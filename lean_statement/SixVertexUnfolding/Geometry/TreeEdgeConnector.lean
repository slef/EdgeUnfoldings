import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! Any two different unoriented edges of a tree are the end edges
of a simple path, after choosing their orientations. -/

namespace SixVertexUnfolding.TreeFrames

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} (tree : G.IsTree)

include tree

/-- Orient an edge away from a chosen root and include it in a simple path. -/
theorem exists_path_ending_with_edge (root : V) {w z : V} (last : G.Adj w z) :
    ∃ (near far : V) (edge : G.Adj near far) (stem : G.Walk root near),
      s(near, far) = s(w, z) ∧ (stem.concat edge).IsPath := by
  classical
  obtain ⟨p, hp, _⟩ := tree.existsUnique_path root w
  obtain ⟨q, hq, _⟩ := tree.existsUnique_path root z
  by_cases before : w ∈ q.support
  · refine ⟨w, z, last, p, rfl, ?_⟩
    rwa [← tree.isAcyclic.path_concat hp hq last before]
  · have other := tree.isAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath hp hq last before
    refine ⟨z, w, last.symm, q, Sym2.eq_swap, ?_⟩
    rwa [← tree.isAcyclic.path_concat hq hp last.symm other]

/-- Include the first edge, keeping an already oriented last edge. -/
theorem extend_to_first_edge {u v w z : V} (first : G.Adj u v) (last : G.Adj w z)
    (different : s(u, v) ≠ s(w, z)) (stem : G.Walk u w)
    (simple : (stem.concat last).IsPath) :
    ∃ (start next : V) (edge : G.Adj start next) (middle : G.Walk next w),
      s(start, next) = s(u, v) ∧ (Walk.cons edge (middle.concat last)).IsPath := by
  classical
  have stem_simple := ((Walk.concat_isPath_iff last).mp simple).1
  by_cases on_stem : v ∈ stem.support
  · obtain ⟨initial, middle, initial_simple, _, split⟩ :=
      stem_simple.mem_support_iff_exists_append.mp on_stem
    have initial_eq : initial = first.toWalk :=
      (tree.existsUnique_path u v).unique initial_simple (Walk.IsPath.of_adj first)
    refine ⟨u, v, first, middle, rfl, ?_⟩
    simpa only [split, initial_eq, SimpleGraph.Adj.toWalk, Walk.cons_append, Walk.nil_append,
      Walk.concat_cons] using simple
  · have not_far : v ≠ z := by
      intro same
      subst z
      have whole_eq : stem.concat last = first.toWalk :=
        (tree.existsUnique_path u v).unique simple (Walk.IsPath.of_adj first)
      have lengths := congrArg Walk.length whole_eq
      have empty : stem.length = 0 := by
        simp only [Walk.length_concat, SimpleGraph.Adj.toWalk, Walk.length_cons,
          Walk.length_nil] at lengths
        omega
      have same_start := Walk.eq_of_length_eq_zero empty
      subst w
      exact different rfl
    have absent : v ∉ (stem.concat last).support := by
      simp [Walk.support_concat, List.concat_eq_append, on_stem, not_far]
    exact ⟨v, u, first.symm, stem, Sym2.eq_swap, simple.cons absent⟩

/-- The common path includes both edges and repeats no vertex. -/
theorem exists_edge_to_edge_path {u v w z : V} (first : G.Adj u v) (last : G.Adj w z)
    (different : s(u, v) ≠ s(w, z)) :
    ∃ (start next near far : V) (first' : G.Adj start next) (last' : G.Adj near far)
      (middle : G.Walk next near),
      s(start, next) = s(u, v) ∧ s(near, far) = s(w, z) ∧
        (Walk.cons first' (middle.concat last')).IsPath := by
  obtain ⟨near, far, last', stem, last_same, simple⟩ := exists_path_ending_with_edge tree u last
  have still_different : s(u, v) ≠ s(near, far) := by rwa [last_same]
  obtain ⟨start, next, first', middle, first_same, whole_simple⟩ :=
    extend_to_first_edge tree first last' still_different stem simple
  exact ⟨start, next, near, far, first', last', middle, first_same, last_same, whole_simple⟩

end SixVertexUnfolding.TreeFrames
