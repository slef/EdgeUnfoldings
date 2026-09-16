import SixVertexUnfolding.Geometry.EdgeHullSeparation
import SixVertexUnfolding.Geometry.SmallPolyhedra
import Mathlib.Analysis.Convex.Radon

/-!
Radon's theorem supplies a nonedge among any five original vertices in three-space.
This excludes the complete five-vertex graph directly from the convex geometry.
-/

namespace SixVertexUnfolding.ConvexPolyhedron

/-- Among five original vertices, some joining segment meets the hull of the other vertices. -/
theorem five_distinct_vertices_have_radon_pair (P : ConvexPolyhedron) (v : Fin 5 → P.Vertex)
    (distinct : Function.Injective v) :
    ∃ i j : Fin 5, i ≠ j ∧
      (segment ℝ (v i : Space) (v j : Space) ∩
        convexHull ℝ ((P.vertices : Set Space) \ {(v i : Space), (v j : Space)})).Nonempty := by
  let point (i : Fin 5) : Space := v i
  have injective : Function.Injective point := Subtype.val_injective.comp distinct
  have dependent : ¬ AffineIndependent ℝ point := by
    intro independent
    have dimension := independent.card_le_finrank_succ
    have upper := Submodule.finrank_le (vectorSpan ℝ (Set.range point))
    have ambient : Module.finrank ℝ Space = 3 := by simp [Space]
    rw [ambient] at upper
    simp only [Fintype.card_fin] at dimension
    omega
  obtain ⟨I, z, zI, zC⟩ := Convex.radon_partition dependent
  have part_size (J : Set (Fin 5)) (x : Space)
      (first : x ∈ convexHull ℝ (point '' J))
      (second : x ∈ convexHull ℝ (point '' Jᶜ)) : 2 ≤ J.ncard := by
    have nonempty : J.Nonempty := Set.image_nonempty.mp (convexHull_nonempty_iff.mp ⟨x, first⟩)
    have positive := nonempty.ncard_pos
    by_contra too_small
    have one : J.ncard = 1 := by omega
    obtain ⟨i, singleton⟩ := Set.ncard_eq_one.mp one
    rw [singleton, Set.image_singleton, convexHull_singleton] at first
    have equal : x = point i := first
    apply P.vertex_not_mem_hull_others (v i)
    rw [equal] at second
    apply convexHull_mono (show point '' Jᶜ ⊆ (P.vertices : Set Space) \ {(v i : Space)} from ?_) second
    rintro y ⟨j, jJ, rfl⟩
    refine ⟨(v j).property, ?_⟩
    intro same
    have ji : j = i := injective same
    exact jJ (by simp [singleton, ji])
  have left_size := part_size I z zI zC
  have right_size := part_size Iᶜ z zC (by simpa only [compl_compl] using zI)
  have total := Set.ncard_add_ncard_compl I
  have total_five : I.ncard + Iᶜ.ncard = 5 := by simpa using total
  have pair_part : ∃ J : Set (Fin 5), J.ncard = 2 ∧
      (convexHull ℝ (point '' J) ∩ convexHull ℝ (point '' Jᶜ)).Nonempty := by
    have sizes : I.ncard = 2 ∨ Iᶜ.ncard = 2 := by omega
    rcases sizes with left | right
    · exact ⟨I, left, z, zI, zC⟩
    · exact ⟨Iᶜ, right, z, zC, by simpa only [compl_compl] using zI⟩
  obtain ⟨J, pair_count, x, on_pair, in_others⟩ := pair_part
  obtain ⟨i, j, ij, pair⟩ := Set.ncard_eq_two.mp pair_count
  have on_segment : x ∈ segment ℝ (point i) (point j) := by
    simpa only [pair, Set.image_insert_eq, Set.image_singleton, convexHull_pair] using on_pair
  have in_hull : x ∈ convexHull ℝ ((P.vertices : Set Space) \ {(point i), (point j)}) := by
    apply convexHull_mono (show point '' Jᶜ ⊆ (P.vertices : Set Space) \ {point i, point j} from ?_) in_others
    rintro y ⟨k, kJ, rfl⟩
    refine ⟨(v k).property, ?_⟩
    rintro (same | same)
    · exact kJ (by rw [pair]; exact Or.inl (injective same))
    · exact kJ (by rw [pair]; exact Or.inr (injective same))
  exact ⟨i, j, ij, x, on_segment, in_hull⟩

/-- Among any five distinct original vertices, some pair is not an original edge. -/
theorem five_distinct_vertices_have_nonedge (P : ConvexPolyhedron) (v : Fin 5 → P.Vertex)
    (distinct : Function.Injective v) :
    ∃ i j : Fin 5, i ≠ j ∧ ¬ P.edgeGraph.Adj (v i) (v j) := by
  obtain ⟨i, j, different, x, on_segment, in_hull⟩ :=
    P.five_distinct_vertices_have_radon_pair v distinct
  exact ⟨i, j, different, fun edge =>
    Set.disjoint_left.mp (P.edge_disjoint_hull_others (v i) (v j) edge) on_segment in_hull⟩

/-- A five-vertex convex polyhedron cannot have the complete vertex-edge graph. -/
theorem five_vertices_have_nonedge (P : ConvexPolyhedron) (size : P.vertices.card = 5) :
    ∃ a b : P.Vertex, a ≠ b ∧ ¬ P.edgeGraph.Adj a b := by
  let index : Fin 5 ≃ P.Vertex := (Fintype.equivFinOfCardEq (P.vertex_card.trans size)).symm
  obtain ⟨i, j, different, nonedge⟩ := P.five_distinct_vertices_have_nonedge index index.injective
  exact ⟨index i, index j, fun same => different (index.injective same), nonedge⟩

end SixVertexUnfolding.ConvexPolyhedron
