import SixVertexUnfolding.Geometry.FacetEdgeCounting

/-! Two-color edge counts for triangles and quadrilaterals. -/

namespace SixVertexUnfolding.ConvexPolyhedron

variable {P : ConvexPolyhedron}

/-- Weight one on same-color endpoint pairs, zero on pairs with different colors. -/
noncomputable def internalEdgeWeight (color : P.Vertex → Bool) : Sym2 P.Vertex → ℕ :=
  Sym2.lift ⟨fun a b => if color a = color b then 1 else 0, fun a b => by simp [eq_comm]⟩

@[simp] theorem internalEdgeWeight_pair (color : P.Vertex → Bool) (a b : P.Vertex) :
    internalEdgeWeight color s(a, b) = if color a = color b then 1 else 0 := rfl

namespace Face

variable (F : P.Face) (color : P.Vertex → Bool)

/-- A two-colored triangle that is not monochromatic has exactly one same-color edge. -/
theorem triangle_internal_edge_sum (a b c : P.Vertex) (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c)
    (vertices : F.val ∩ (P.vertices : Set Space) = {(a : Space), (b : Space), (c : Space)})
    (not_monochrome : ¬ (color a = color b ∧ color b = color c)) :
    ∑ e ∈ F.edgeFinset, internalEdgeWeight color e = 1 := by
  classical
  rw [F.triangle_edgeFinset a b c ab ac bc vertices]
  simp [ab, ac, bc, Ne.symm ab, Ne.symm bc]
  cases ha : color a <;> cases hb : color b <;> cases hc : color c <;> simp_all [internalEdgeWeight]

namespace Quadrilateral

variable {F color} (Q : F.Quadrilateral)

/-- If all cross-color pairs are edges, a quadrilateral alternates its two colors. -/
theorem colors_alternate
    (across : ∀ a b : P.Vertex, color a ≠ color b → P.edgeGraph.Adj a b)
    (not_monochrome : ¬ ∀ i : Fin 4, color (Q.corner i) = color (Q.corner 0)) (i : Fin 4) :
    color (Q.corner i) ≠ color (Q.corner (i + 1)) := by
  have opposite (j : Fin 4) : color (Q.corner j) = color (Q.corner (j + 2)) := by
    by_contra different
    exact Q.diagonal_not_adjacent j (across _ _ different)
  have first : color (Q.corner 0) = color (Q.corner 2) := opposite 0
  have second : color (Q.corner 1) = color (Q.corner 3) := opposite 1
  have unequal : color (Q.corner 0) ≠ color (Q.corner 1) := by
    intro same
    apply not_monochrome
    intro j
    fin_cases j
    · rfl
    · exact same.symm
    · exact first.symm
    · exact second.symm.trans same.symm
  fin_cases i
  · exact unequal
  · change color (Q.corner 1) ≠ color (Q.corner 2)
    simpa only [← first] using unequal.symm
  · change color (Q.corner 2) ≠ color (Q.corner 3)
    simpa only [← first, ← second] using unequal
  · change color (Q.corner 3) ≠ color (Q.corner 0)
    simpa only [← second] using unequal.symm

/-- Every edge of such a quadrilateral has endpoints of different colors. -/
theorem internal_edge_sum_zero
    (across : ∀ a b : P.Vertex, color a ≠ color b → P.edgeGraph.Adj a b)
    (not_monochrome : ¬ ∀ i : Fin 4, color (Q.corner i) = color (Q.corner 0)) :
    ∑ e ∈ F.edgeFinset, internalEdgeWeight color e = 0 := by
  classical
  rw [Q.edgeFinset_eq_sides, Finset.sum_image (fun i _ j _ same => Q.side_injective same)]
  apply Finset.sum_eq_zero
  intro i _
  simp only [internalEdgeWeight_pair, if_neg (Q.colors_alternate across not_monochrome i)]

end Quadrilateral
end Face

end SixVertexUnfolding.ConvexPolyhedron
