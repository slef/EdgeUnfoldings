import SixVertexUnfolding.Geometry.CutTreeAngleAccounting
import SixVertexUnfolding.Geometry.OctahedralAngles

/-! Transfer the six actual original curvatures to the cut-tree vertices.
The source is absent from the tree; all other original vertices occur
exactly once, and subdivision vertices contribute zero. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Real Set
open scoped BigOperators

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
  {a : frontier P.body} (T : P.CutLocusTree a)

/-- Original vertex curvature, extended by zero to the other tree vertices. -/
noncomputable def cutTreeCurvature (u : T.vertices) : ℝ :=
  ∑ i : Fin 6, if (graph.vertex i : Space) = (u : Space) then graph.curvature i else 0

theorem cutTreeCurvature_at_original (u : T.vertices) (i : Fin 6)
    (at_vertex : (u : Space) = (graph.vertex i : Space)) :
    graph.cutTreeCurvature T u = graph.curvature i := by
  classical
  have equal (j : Fin 6) : (graph.vertex j : Space) = (u : Space) ↔ j = i := by
    rw [at_vertex]
    exact ⟨fun h => graph.vertex.injective (Subtype.ext h), fun h => h ▸ rfl⟩
  simp [cutTreeCurvature, equal]

theorem cutTreeCurvature_at_nonvertex (u : T.vertices) (not_vertex : (u : Space) ∉ P.vertices) :
    graph.cutTreeCurvature T u = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro i _
  apply if_neg
  intro equal
  exact not_vertex (equal ▸ (graph.vertex i).property)

/-- The cut tree contains precisely the original curvature other than the source's. -/
theorem sum_cutTreeCurvature [Fintype T.vertices] (source : Fin 6)
    (at_source : (a : Space) = (graph.vertex source : Space)) :
    ∑ u, graph.cutTreeCurvature T u = 4 * π - graph.curvature source := by
  classical
  have vertex_sum (i : Fin 6) :
      (∑ u : T.vertices, if (graph.vertex i : Space) = (u : Space) then graph.curvature i else 0) =
        if i = source then 0 else graph.curvature i := by
    by_cases same : i = source
    · subst i
      rw [if_pos rfl]
      apply Finset.sum_eq_zero
      intro u _
      apply if_neg
      intro equal
      exact T.vertex_ne_source u (equal.symm.trans at_source.symm)
    · rw [if_neg same]
      have different : (graph.vertex i : Space) ≠ (a : Space) := by
        intro equal
        exact same (graph.vertex.injective (Subtype.ext (equal.trans at_source)))
      let v : T.vertices := ⟨graph.vertex i, T.original_vertex_mem (graph.vertex i).property different⟩
      have equal (u : T.vertices) : (graph.vertex i : Space) = (u : Space) ↔ u = v :=
        ⟨fun h => Subtype.ext h.symm, fun h => by subst u; rfl⟩
      simp only [equal]
      simp
  simp only [cutTreeCurvature]
  rw [Finset.sum_comm]
  simp_rw [vertex_sum]
  have remove : (∑ i : Fin 6, if i = source then 0 else graph.curvature i) =
      (∑ i : Fin 6, graph.curvature i) - graph.curvature source := by
    calc
      _ = ∑ i : Fin 6, (graph.curvature i - if i = source then graph.curvature source else 0) := by
        apply Finset.sum_congr rfl
        intro i _
        split_ifs with same
        · simp [same]
        · simp
      _ = _ := by rw [Finset.sum_sub_distrib]; simp
  rw [remove, graph.sum_curvature]

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
