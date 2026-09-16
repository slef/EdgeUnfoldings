import SixVertexUnfolding.OriginalCutSelection

/-! A direct original-edge construction for the prism-with-diagonal when both degree-four endpoints are the sharper poles. -/

namespace SixVertexUnfolding

/-- A tied maximum can always be chosen away from a forbidden diagonal endpoint. -/
theorem equator_maximum_avoiding (curvature : Fin 4 → ℝ) (forbidden other : Fin 4)
    (different : other ≠ forbidden) (comparison : curvature forbidden ≤ curvature other) :
    ∃ slit, slit ≠ forbidden ∧ ∀ i, curvature i ≤ curvature slit := by
  obtain ⟨slit, maximal⟩ := Curvature.equator_has_maximum curvature
  by_cases same : slit = forbidden
  · subst slit
    exact ⟨other, different, fun i => (maximal i).trans comparison⟩
  · exact ⟨slit, same, maximal⟩

namespace ConvexPolyhedron.SixVertexGraph

open OctahedralTriangles

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
variable (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include small_faces in
/-- Comparing the two forbidden endpoints selects a slit that retains both original quadrilaterals. -/
theorem hasEdgeUnfolding_of_prismDiagonal_sharper_endpoints (kind : graph.kind = .prismDiagonal)
    (first_order : graph.curvature 1 ≤ graph.curvature 0)
    (last_order : graph.curvature 4 ≤ graph.curvature 5) : P.HasEdgeUnfolding := by
  rcases le_total (graph.curvature 2) (graph.curvature 3) with first | last
  · obtain ⟨slit, avoids, maximal⟩ := equator_maximum_avoiding
      (fun i => graph.curvature (fanNeighbor 0 i)) 0 2 (by decide) first
    apply graph.hasEdgeUnfolding_of_original_cut_selection small_faces 0 slit first_order maximal
    · intro j
      apply (graph.edges _ _).mpr
      rw [kind]
      exact (by decide : ∀ j, SmallGraphs.SixGraphKind.prismDiagonal.adjacent 0 (fanNeighbor 0 j)) j
    · apply (graph.edges _ _).mpr
      rw [kind]
      exact (by decide : ∀ slit : Fin 4, slit ≠ 0 →
        SmallGraphs.SixGraphKind.prismDiagonal.adjacent (opposite 0) (fanNeighbor 0 slit)) slit avoids
  · obtain ⟨slit, avoids, maximal⟩ := equator_maximum_avoiding
      (fun i => graph.curvature (fanNeighbor 5 i)) 3 1 (by decide) last
    apply graph.hasEdgeUnfolding_of_original_cut_selection small_faces 5 slit last_order maximal
    · intro j
      apply (graph.edges _ _).mpr
      rw [kind]
      exact (by decide : ∀ j, SmallGraphs.SixGraphKind.prismDiagonal.adjacent 5 (fanNeighbor 5 j)) j
    · apply (graph.edges _ _).mpr
      rw [kind]
      exact (by decide : ∀ slit : Fin 4, slit ≠ 3 →
        SmallGraphs.SixGraphKind.prismDiagonal.adjacent (opposite 5) (fanNeighbor 5 slit)) slit avoids

end ConvexPolyhedron.SixVertexGraph
end SixVertexUnfolding
