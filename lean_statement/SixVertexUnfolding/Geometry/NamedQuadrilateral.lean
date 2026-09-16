import SixVertexUnfolding.Geometry.QuadrilateralEdges
import SixVertexUnfolding.Geometry.QuadrilateralSplit

/-! Work with four named corners of a quadrilateral, rather than an arbitrary cyclic enumeration. -/

namespace SixVertexUnfolding.ConvexPolyhedron.Face

variable {P : ConvexPolyhedron} {F : P.Face}

/-- Distinct quadrilateral corners are nonadjacent exactly when they are opposite corners. -/
theorem Quadrilateral.opposite_of_nonedge (Q : F.Quadrilateral) (i j : Fin 4)
    (different : i ≠ j) (nonedge : ¬ P.edgeGraph.Adj (Q.corner i) (Q.corner j)) : j = i + 2 := by
  have not_consecutive : ¬ (j = i + 1 ∨ i = j + 1) :=
    fun consecutive => nonedge ((Q.adjacent_iff_consecutive i j).mpr consecutive)
  exact (by decide : ∀ i j : Fin 4, i ≠ j → ¬ (j = i + 1 ∨ i = j + 1) → j = i + 2)
    i j different not_consecutive

/-- Specifying the four corners and their two nonedge diagonals gives the strict crossing. -/
theorem quadrilateral_crossing_of_nonedge (F : P.Face)
    (four : (F.val ∩ (P.vertices : Set Space)).ncard = 4)
    (v : Fin 4 → P.Vertex) (distinct : Function.Injective v)
    (on_face : ∀ i, (v i : Space) ∈ F.val)
    (first_nonedge : ¬ P.edgeGraph.Adj (v 0) (v 2))
    (second_nonedge : ¬ P.edgeGraph.Adj (v 1) (v 3)) :
    ∃ q : Space, q ∈ openSegment ℝ (v 0 : Space) (v 2 : Space) ∧
      q ∈ openSegment ℝ (v 1 : Space) (v 3 : Space) := by
  classical
  obtain ⟨Q⟩ := F.exists_quadrilateral four
  have corner_exists (i : Fin 4) : ∃ j, Q.corner j = v i := by
    have member : (v i : Space) ∈ F.val ∩ (P.vertices : Set Space) := ⟨on_face i, (v i).property⟩
    rw [Q.vertices] at member
    obtain ⟨j, same⟩ := member
    exact ⟨j, Subtype.ext same⟩
  choose label label_vertex using corner_exists
  have injective : Function.Injective label := by
    intro i j same
    apply distinct
    rw [← label_vertex i, ← label_vertex j, same]
  have opposite02 : label 2 = label 0 + 2 := Q.opposite_of_nonedge _ _
    (injective.ne (by decide)) (by rwa [label_vertex, label_vertex])
  have opposite13 : label 3 = label 1 + 2 := Q.opposite_of_nonedge _ _
    (injective.ne (by decide)) (by rwa [label_vertex, label_vertex])
  obtain ⟨q, first, second⟩ := Q.cyclic_crossing (label 0)
  rw [← opposite02, label_vertex, label_vertex] at first
  have neighbor : label 1 = label 0 + 1 ∨ label 1 = label 0 + 3 := by
    have ne0 : label 1 ≠ label 0 := injective.ne (by decide)
    have ne2 : label 1 ≠ label 0 + 2 := by rw [← opposite02]; exact injective.ne (by decide)
    exact (by decide : ∀ i j : Fin 4, j ≠ i → j ≠ i + 2 → j = i + 1 ∨ j = i + 3)
      (label 0) (label 1) ne0 ne2
  refine ⟨q, first, ?_⟩
  rcases neighbor with forward | reverse
  · have last : label 3 = label 0 + 3 := by
      rw [opposite13, forward]
      exact (by decide : ∀ i : Fin 4, i + 1 + 2 = i + 3) _
    rwa [← forward, ← last, label_vertex, label_vertex] at second
  · have last : label 3 = label 0 + 1 := by
      rw [opposite13, reverse]
      exact (by decide : ∀ i : Fin 4, i + 3 + 2 = i + 1) _
    rw [← last, ← reverse, label_vertex, label_vertex] at second
    rwa [openSegment_symm]

/-- A specified nonedge diagonal decomposes the whole facet into the two expected triangles. -/
theorem split_named_quadrilateral (F : P.Face)
    (v : Fin 4 → P.Vertex) (distinct : Function.Injective v)
    (vertices : F.val ∩ (P.vertices : Set Space) = Set.range (fun i => (v i : Space)))
    (first_nonedge : ¬ P.edgeGraph.Adj (v 0) (v 2))
    (second_nonedge : ¬ P.edgeGraph.Adj (v 1) (v 3)) :
    F.val = convexHull ℝ ({(v 0 : Space), (v 1 : Space), (v 2 : Space)} : Set Space) ∪
      convexHull ℝ ({(v 0 : Space), (v 2 : Space), (v 3 : Space)} : Set Space) := by
  have point_injective : Function.Injective (fun i => (v i : Space)) :=
    fun _ _ same => distinct (Subtype.ext same)
  have four : (F.val ∩ (P.vertices : Set Space)).ncard = 4 := by
    rw [vertices, Set.ncard_range_of_injective point_injective]
    simp
  have on_face (i : Fin 4) : (v i : Space) ∈ F.val := by
    have member : (v i : Space) ∈ F.val ∩ (P.vertices : Set Space) := by rw [vertices]; exact ⟨i, rfl⟩
    exact member.1
  exact (show F.Quadrilateral from {
    corner := v
    distinct := distinct
    vertices := vertices
    crossing := F.quadrilateral_crossing_of_nonedge four v distinct on_face first_nonedge second_nonedge
  }).face_eq_two_triangles

end SixVertexUnfolding.ConvexPolyhedron.Face
