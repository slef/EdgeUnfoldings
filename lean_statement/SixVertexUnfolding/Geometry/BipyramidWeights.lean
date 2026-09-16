import SixVertexUnfolding.Geometry.BipyramidRadon
import SixVertexUnfolding.Geometry.TriangleWeights

/-! The strict Radon crossing supplies the positive weights needed by the metric identity. -/

namespace SixVertexUnfolding.ConvexPolyhedron.BipyramidVertices

variable {P : ConvexPolyhedron} (B : BipyramidVertices P)

/-- Any three distinct equator indices list the entire equator triangle. -/
theorem equatorPoints_eq_triple (source i j : Fin 3)
    (si : source ≠ i) (sj : source ≠ j) (ij : i ≠ j) :
    B.equatorPoints = {(B.equatorVertex source : Space), (B.equatorVertex i : Space),
      (B.equatorVertex j : Space)} := by
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    have choices : k = source ∨ k = i ∨ k = j := by omega
    rcases choices with rfl | rfl | rfl <;> simp
  · rintro (rfl | rfl | rfl)
    exacts [⟨source, rfl⟩, ⟨i, rfl⟩, ⟨j, rfl⟩]

/-- Both poles and all three equator vertices have positive coefficients in the affine relation. -/
theorem exists_positive_radon_weights (size : P.vertices.card = 5) (upper : Bool)
    (source i j : Fin 3) (si : source ≠ i) (sj : source ≠ j) (ij : i ≠ j) :
    ∃ a b s u v : ℝ, 0 < a ∧ 0 < b ∧ 0 < s ∧ 0 < u ∧ 0 < v ∧
      a + b = s + u + v ∧
      a • (B.poleVertex upper : Space) + b • (B.poleVertex (!upper) : Space) =
        s • (B.equatorVertex source : Space) + u • (B.equatorVertex i : Space) +
          v • (B.equatorVertex j : Space) := by
  obtain ⟨q, on_poles, in_equator, off_edges⟩ := B.strict_equator_crossing size
  have on_chosen_poles : q ∈ openSegment ℝ (B.poleVertex upper : Space) (B.poleVertex (!upper) : Space) := by
    cases upper
    · simpa only [poleVertex, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_eq,
        openSegment_symm ℝ (B.bottom : Space) (B.top : Space)] using on_poles
    · exact on_poles
  obtain ⟨a, b, a_pos, b_pos, pole_total, pole_combination⟩ := on_chosen_poles
  rw [B.equatorPoints_eq_triple source i j si sj ij] at in_equator
  obtain ⟨s, u, v, s_pos, u_pos, v_pos, equator_total, equator_combination⟩ :=
    triangle_positive_weights (B.equatorVertex source : Space) (B.equatorVertex i : Space)
      (B.equatorVertex j : Space) q in_equator (off_edges source i si)
      (off_edges source j sj) (off_edges i j ij)
  exact ⟨a, b, s, u, v, a_pos, b_pos, s_pos, u_pos, v_pos,
    pole_total.trans equator_total.symm, pole_combination.trans equator_combination.symm⟩

end SixVertexUnfolding.ConvexPolyhedron.BipyramidVertices
