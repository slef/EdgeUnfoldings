import SixVertexUnfolding.PrismDiagonalSelection

/-! Larger explicit curvature regions in which a maximum slit is an original edge. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open OctahedralTriangles

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
variable (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include small_faces in
/-- Source 0 works whenever it is the sharper pole and vertex 2 is not the unique equator maximum. -/
theorem hasEdgeUnfolding_of_prismDiagonal_first_region (kind : graph.kind = .prismDiagonal)
    (source_order : graph.curvature 1 ≤ graph.curvature 0)
    (slit_order : graph.curvature 2 ≤ max (graph.curvature 3) (max (graph.curvature 4) (graph.curvature 5))) :
    P.HasEdgeUnfolding := by
  have alternative : ∃ other : Fin 4, other ≠ 0 ∧
      graph.curvature (fanNeighbor 0 0) ≤ graph.curvature (fanNeighbor 0 other) := by
    rcases le_max_iff.mp slit_order with h | h
    · exact ⟨2, by decide, h⟩
    rcases le_max_iff.mp h with h | h
    · exact ⟨1, by decide, h⟩
    · exact ⟨3, by decide, h⟩
  obtain ⟨other, different, comparison⟩ := alternative
  obtain ⟨slit, avoids, maximal⟩ := equator_maximum_avoiding
    (fun i => graph.curvature (fanNeighbor 0 i)) 0 other different comparison
  apply graph.hasEdgeUnfolding_of_original_cut_selection small_faces 0 slit source_order maximal
  · intro j
    apply (graph.edges _ _).mpr
    rw [kind]
    exact (by decide : ∀ j, SmallGraphs.SixGraphKind.prismDiagonal.adjacent 0 (fanNeighbor 0 j)) j
  · apply (graph.edges _ _).mpr
    rw [kind]
    exact (by decide : ∀ slit : Fin 4, slit ≠ 0 →
      SmallGraphs.SixGraphKind.prismDiagonal.adjacent (opposite 0) (fanNeighbor 0 slit)) slit avoids

include small_faces in
/-- Source 5 gives the reflected region, with all equality cases included. -/
theorem hasEdgeUnfolding_of_prismDiagonal_last_region (kind : graph.kind = .prismDiagonal)
    (source_order : graph.curvature 4 ≤ graph.curvature 5)
    (slit_order : graph.curvature 3 ≤ max (graph.curvature 0) (max (graph.curvature 1) (graph.curvature 2))) :
    P.HasEdgeUnfolding := by
  have alternative : ∃ other : Fin 4, other ≠ 3 ∧
      graph.curvature (fanNeighbor 5 3) ≤ graph.curvature (fanNeighbor 5 other) := by
    rcases le_max_iff.mp slit_order with h | h
    · exact ⟨0, by decide, h⟩
    rcases le_max_iff.mp h with h | h
    · exact ⟨2, by decide, h⟩
    · exact ⟨1, by decide, h⟩
  obtain ⟨other, different, comparison⟩ := alternative
  obtain ⟨slit, avoids, maximal⟩ := equator_maximum_avoiding
    (fun i => graph.curvature (fanNeighbor 5 i)) 3 other different comparison
  apply graph.hasEdgeUnfolding_of_original_cut_selection small_faces 5 slit source_order maximal
  · intro j
    apply (graph.edges _ _).mpr
    rw [kind]
    exact (by decide : ∀ j, SmallGraphs.SixGraphKind.prismDiagonal.adjacent 5 (fanNeighbor 5 j)) j
  · apply (graph.edges _ _).mpr
    rw [kind]
    exact (by decide : ∀ slit : Fin 4, slit ≠ 3 →
      SmallGraphs.SixGraphKind.prismDiagonal.adjacent (opposite 5) (fanNeighbor 5 slit)) slit avoids

include small_faces in
/-- Outside the completed regions, each eligible source has one strictly forbidden maximum. -/
theorem prismDiagonal_unfolding_or_strict_obstructions (kind : graph.kind = .prismDiagonal) :
    P.HasEdgeUnfolding ∨
      ((graph.curvature 0 < graph.curvature 1 ∨
        max (graph.curvature 3) (max (graph.curvature 4) (graph.curvature 5)) < graph.curvature 2) ∧
       (graph.curvature 5 < graph.curvature 4 ∨
        max (graph.curvature 0) (max (graph.curvature 1) (graph.curvature 2)) < graph.curvature 3)) := by
  by_cases first : graph.curvature 1 ≤ graph.curvature 0 ∧
      graph.curvature 2 ≤ max (graph.curvature 3) (max (graph.curvature 4) (graph.curvature 5))
  · exact Or.inl (graph.hasEdgeUnfolding_of_prismDiagonal_first_region small_faces kind first.1 first.2)
  by_cases last : graph.curvature 4 ≤ graph.curvature 5 ∧
      graph.curvature 3 ≤ max (graph.curvature 0) (max (graph.curvature 1) (graph.curvature 2))
  · exact Or.inl (graph.hasEdgeUnfolding_of_prismDiagonal_last_region small_faces kind last.1 last.2)
  push Not at first last
  refine Or.inr ⟨?_, ?_⟩
  · by_cases h : graph.curvature 1 ≤ graph.curvature 0
    · exact Or.inr (first h)
    · exact Or.inl (lt_of_not_ge h)
  · by_cases h : graph.curvature 4 ≤ graph.curvature 5
    · exact Or.inr (last h)
    · exact Or.inl (lt_of_not_ge h)

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
