import SixVertexUnfolding.Geometry.SmallPolyhedronCurvature
import SixVertexUnfolding.Geometry.CutTreeAngleAccounting

/-! Transfer actual original-vertex curvature to the cut tree.
The source is absent; every other original vertex occurs exactly once. -/

namespace SixVertexUnfolding.ConvexPolyhedron.CutLocusTree

open Set Real

variable {P : ConvexPolyhedron} [Fintype P.Face]
  {a : frontier P.body} (T : P.CutLocusTree a)

/-- Original curvature on tree vertices, with zero at subdivision vertices. -/
noncomputable def originalCurvature (u : T.vertices) : ℝ :=
  ∑ v : P.Vertex, if (v : Space) = (u : Space) then P.vertexCurvature v else 0

theorem originalCurvature_at_vertex (u : T.vertices) (v : P.Vertex)
    (at_vertex : (u : Space) = (v : Space)) : T.originalCurvature u = P.vertexCurvature v := by
  classical
  have equal (w : P.Vertex) : (w : Space) = (u : Space) ↔ w = v := by
    rw [at_vertex]
    exact Subtype.coe_inj
  simp [originalCurvature, equal]

theorem originalCurvature_at_nonvertex (u : T.vertices) (not_vertex : (u : Space) ∉ P.vertices) :
    T.originalCurvature u = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro v _
  apply if_neg
  intro equal
  exact not_vertex (equal ▸ v.property)

/-- Summation loses precisely the source's curvature. -/
theorem sum_originalCurvature [Fintype T.vertices] (source : P.Vertex)
    (at_source : (a : Space) = (source : Space)) :
    (∑ u, T.originalCurvature u) = (∑ v : P.Vertex, P.vertexCurvature v) - P.vertexCurvature source := by
  classical
  have vertex_sum (v : P.Vertex) :
      (∑ u : T.vertices, if (v : Space) = (u : Space) then P.vertexCurvature v else 0) =
        if v = source then 0 else P.vertexCurvature v := by
    by_cases same : v = source
    · subst v
      rw [if_pos rfl]
      apply Finset.sum_eq_zero
      intro u _
      apply if_neg
      intro equal
      exact T.vertex_ne_source u (equal.symm.trans at_source.symm)
    · rw [if_neg same]
      have different : (v : Space) ≠ (a : Space) := by
        intro equal
        exact same (Subtype.ext (equal.trans at_source))
      let w : T.vertices := ⟨v, T.original_vertex_mem v.property different⟩
      have equal (u : T.vertices) : (v : Space) = (u : Space) ↔ u = w :=
        ⟨fun h => Subtype.ext h.symm, fun h => by subst u; rfl⟩
      simp only [equal]
      simp
  simp only [originalCurvature]
  rw [Finset.sum_comm]
  simp_rw [vertex_sum]
  calc
    _ = ∑ v : P.Vertex, (P.vertexCurvature v - if v = source then P.vertexCurvature source else 0) := by
      apply Finset.sum_congr rfl
      intro v _
      split_ifs with same
      · simp [same]
      · simp
    _ = _ := by rw [Finset.sum_sub_distrib]; simp

end SixVertexUnfolding.ConvexPolyhedron.CutLocusTree
