import SixVertexUnfolding.Geometry.FacetEdges
import SixVertexUnfolding.Geometry.EdgeHullSeparation
import Mathlib.Analysis.Convex.Radon

/-! Four vertices of an original quadrilateral, ordered by their crossing diagonals. -/

namespace SixVertexUnfolding.ConvexPolyhedron

/-- A Radon part of original vertices contains at least two vertices. -/
theorem radon_part_card_ge_two {ι : Type*} [Fintype ι] (P : ConvexPolyhedron)
    (v : ι → P.Vertex) (distinct : Function.Injective v) (part : Set ι) (x : Space)
    (first : x ∈ convexHull ℝ ((fun i => (v i : Space)) '' part))
    (second : x ∈ convexHull ℝ ((fun i => (v i : Space)) '' partᶜ)) :
    2 ≤ part.ncard := by
  have nonempty := Set.image_nonempty.mp (convexHull_nonempty_iff.mp ⟨x, first⟩)
  have positive := nonempty.ncard_pos
  by_contra too_small
  obtain ⟨i, singleton⟩ := Set.ncard_eq_one.mp (show part.ncard = 1 by omega)
  rw [singleton, Set.image_singleton, convexHull_singleton] at first
  have equal : x = (v i : Space) := first
  apply P.vertex_not_mem_hull_others (v i)
  rw [equal] at second
  apply convexHull_mono (show (fun j => (v j : Space)) '' partᶜ ⊆
    (P.vertices : Set Space) \ {(v i : Space)} from ?_) second
  rintro y ⟨j, outside, rfl⟩
  refine ⟨(v j).property, ?_⟩
  intro same
  exact outside (by rw [singleton]; exact distinct (Subtype.ext same))

namespace Face

variable {P : ConvexPolyhedron} (F : P.Face)

/-- The four original corners, in an order whose two diagonals cross in their interiors. -/
structure Quadrilateral where
  corner : Fin 4 → P.Vertex
  distinct : Function.Injective corner
  vertices : F.val ∩ (P.vertices : Set Space) = Set.range (fun i => (corner i : Space))
  crossing : ∃ x : Space, x ∈ openSegment ℝ (corner 0 : Space) (corner 2 : Space) ∧
    x ∈ openSegment ℝ (corner 1 : Space) (corner 3 : Space)

/-- Four original vertices in one facet are affinely dependent. -/
theorem four_vertices_dependent (v : Fin 4 → P.Vertex)
    (on_face : ∀ i, (v i : Space) ∈ F.val) :
    ¬ AffineIndependent ℝ (fun i => (v i : Space)) := by
  intro independent
  have dimension := independent.card_le_finrank_succ
  have inclusion : vectorSpan ℝ (Set.range (fun i => (v i : Space))) ≤ vectorSpan ℝ F.val :=
    vectorSpan_mono ℝ (by rintro x ⟨i, rfl⟩; exact on_face i)
  have upper := Submodule.finrank_mono inclusion
  have face_dimension : Module.finrank ℝ (vectorSpan ℝ F.val) = 2 := by
    have dimension := F.property.1
    change Module.finrank ℝ (affineSpan ℝ F.val).direction = 2 at dimension
    rwa [direction_affineSpan] at dimension
  rw [face_dimension] at upper
  simp only [Fintype.card_fin] at dimension
  omega

/-- Every actual quadrilateral facet admits a cyclic order of its four genuine vertices. -/
theorem exists_quadrilateral (four : (F.val ∩ (P.vertices : Set Space)).ncard = 4) :
    Nonempty F.Quadrilateral := by
  classical
  let W := F.val ∩ (P.vertices : Set Space)
  have finite : W.Finite := P.vertices.finite_toSet.inter_of_right F.val
  letI : Fintype W := finite.fintype
  have count : Fintype.card W = 4 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    exact four
  let index : Fin 4 ≃ W := (Fintype.equivFinOfCardEq count).symm
  let v (i : Fin 4) : P.Vertex := ⟨index i, (index i).property.2⟩
  let point (i : Fin 4) : Space := v i
  have distinct : Function.Injective v := by
    intro i j same
    apply index.injective
    exact Subtype.ext (congrArg (fun w : P.Vertex => (w : Space)) same)
  have on_face (i : Fin 4) : (v i : Space) ∈ F.val := (index i).property.1
  have range_eq : W = Set.range point := by
    ext x
    constructor
    · intro member
      obtain ⟨i, equal⟩ := index.surjective ⟨x, member⟩
      exact ⟨i, congrArg Subtype.val equal⟩
    · rintro ⟨i, rfl⟩
      exact (index i).property
  obtain ⟨part, x, first, second⟩ := Convex.radon_partition (F.four_vertices_dependent v on_face)
  have left_size := P.radon_part_card_ge_two v distinct part x first second
  have right_size := P.radon_part_card_ge_two v distinct partᶜ x second
    (by simpa only [compl_compl] using first)
  have total : part.ncard + partᶜ.ncard = 4 := by simpa using Set.ncard_add_ncard_compl part
  obtain ⟨a, c, ac, left_pair⟩ := Set.ncard_eq_two.mp (show part.ncard = 2 by omega)
  obtain ⟨b, d, bd, right_pair⟩ := Set.ncard_eq_two.mp (show partᶜ.ncard = 2 by omega)
  have separate (i j : Fin 4) (hi : i ∈ ({a, c} : Set (Fin 4)))
      (hj : j ∈ ({b, d} : Set (Fin 4))) : i ≠ j := by
    intro same
    have outside : j ∈ partᶜ := right_pair ▸ hj
    exact outside (same ▸ (left_pair ▸ hi))
  have ab : a ≠ b := separate a b (Or.inl rfl) (Or.inl rfl)
  have ad : a ≠ d := separate a d (Or.inl rfl) (Or.inr rfl)
  have cb : c ≠ b := separate c b (Or.inr rfl) (Or.inl rfl)
  have cd : c ≠ d := separate c d (Or.inr rfl) (Or.inr rfl)
  let order : Fin 4 → Fin 4 := ![a, b, c, d]
  have order_injective : Function.Injective order := by
    intro i j same
    fin_cases i <;> fin_cases j <;> simp [order] at same ⊢ <;> grind
  have order_surjective := (Finite.injective_iff_surjective).mp order_injective
  have left_segment : x ∈ segment ℝ (v a : Space) (v c : Space) := by
    simpa only [left_pair, Set.image_insert_eq, Set.image_singleton, convexHull_pair] using first
  have right_segment : x ∈ segment ℝ (v b : Space) (v d : Space) := by
    simpa only [right_pair, Set.image_insert_eq, Set.image_singleton, convexHull_pair] using second
  have not_endpoint (i j k : Fin 4) (ij : i ≠ j) (ik : i ≠ k)
      (on_segment : x ∈ segment ℝ (v j : Space) (v k : Space)) : (v i : Space) ≠ x := by
    intro same
    apply P.vertex_not_mem_hull_others (v i)
    rw [← same, ← convexHull_pair] at on_segment
    apply convexHull_mono (show {(v j : Space), (v k : Space)} ⊆
      (P.vertices : Set Space) \ {(v i : Space)} from ?_) on_segment
    rintro y (rfl | rfl)
    · exact ⟨(v j).property, fun equal => ij (distinct (Subtype.ext equal.symm))⟩
    · exact ⟨(v k).property, fun equal => ik (distinct (Subtype.ext equal.symm))⟩
  refine ⟨{
    corner := fun i => v (order i)
    distinct := distinct.comp order_injective
    vertices := ?_
    crossing := ⟨x, mem_openSegment_of_ne_left_right
      (not_endpoint a b d ab ad right_segment) (not_endpoint c b d cb cd right_segment) left_segment,
      mem_openSegment_of_ne_left_right (not_endpoint b a c ab.symm cb.symm left_segment)
        (not_endpoint d a c ad.symm cd.symm left_segment) right_segment⟩
  }⟩
  change W = Set.range (point ∘ order)
  rw [Set.range_comp, order_surjective.range_eq, Set.image_univ]
  exact range_eq

end Face
end SixVertexUnfolding.ConvexPolyhedron
