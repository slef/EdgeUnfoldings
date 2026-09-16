import SixVertexUnfolding.Geometry.OctahedralSubdivision

/-! The eight subdivision triangles cover exactly the original whole facets. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open OctahedralTriangles

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include small_faces in
/-- Each canonical quadrilateral is split along its designated auxiliary diagonal. -/
theorem quad_eq_subdivision_triangles (q : Fin 3) (present : quadVertices q ∈ graph.kind.facets) :
    graph.labeledHull (quadVertices q) =
      graph.triangle (quadPieces q 0) ∪ graph.triangle (quadPieces q 1) := by
  obtain ⟨F, labels⟩ := (graph.exists_facet_iff small_faces _).mpr present
  let v (i : Fin 4) : P.Vertex := graph.vertex (quadCorner q i)
  have distinct : Function.Injective v := graph.vertex.injective.comp (quadCorner_injective q)
  have vertices : F.val ∩ (P.vertices : Set Space) = Set.range (fun i => (v i : Space)) := by
    rw [← F.image_vertexLabels graph.vertex, labels]
    simp [quadVertices, v]
    rw [← Set.range_comp]
    rfl
  have diagonals := quad_nonedge_diagonals graph.kind q present
  have split := F.split_named_quadrilateral v distinct vertices
    (fun edge => diagonals.1 ((graph.edges _ _).mp edge))
    (fun edge => diagonals.2 ((graph.edges _ _).mp edge))
  rw [graph.face_eq_labeledHull F, labels] at split
  rw [triangle, triangle, (quad_piece_vertices q).1, (quad_piece_vertices q).2,
    graph.labeledHull_triple, graph.labeledHull_triple]
  exact split

/-- All pieces assigned to an original facet, together, are exactly that whole facet. -/
theorem face_eq_subdivision_triangles (F : P.Face) :
    F.val = ⋃ (t : Fin 8) (_ : graph.triangleFace small_faces t = F), graph.triangle t := by
  have present : F.vertexLabels graph.vertex ∈ graph.kind.facets :=
    (graph.exists_facet_iff small_faces _).mp ⟨F, rfl⟩
  have same_carrier (t : Fin 8) (labels : carrier graph.kind t = F.vertexLabels graph.vertex) :
      graph.triangleFace small_faces t = F := by
    apply Face.vertexLabels_injective graph.vertex
    change (graph.triangleFace small_faces t).vertexLabels graph.vertex = F.vertexLabels graph.vertex
    rw [graph.triangleFace_labels]
    exact labels
  apply Set.Subset.antisymm
  · intro x on_face
    rcases facet_cases graph.kind _ present with ⟨t, carrier_eq, vertices_eq⟩ | ⟨q, vertices_eq, carrier_eq⟩
    · have on_triangle : x ∈ graph.triangle t := by
        rw [triangle, vertices_eq, ← graph.face_eq_labeledHull]
        exact on_face
      exact Set.mem_iUnion.mpr ⟨t, Set.mem_iUnion.mpr ⟨same_carrier t carrier_eq, on_triangle⟩⟩
    · have present_quad : quadVertices q ∈ graph.kind.facets := vertices_eq ▸ present
      rw [graph.face_eq_labeledHull F, ← vertices_eq, graph.quad_eq_subdivision_triangles small_faces q present_quad] at on_face
      rcases on_face with first | second
      · exact Set.mem_iUnion.mpr ⟨quadPieces q 0,
          Set.mem_iUnion.mpr ⟨same_carrier _ (carrier_eq 0), first⟩⟩
      · exact Set.mem_iUnion.mpr ⟨quadPieces q 1,
          Set.mem_iUnion.mpr ⟨same_carrier _ (carrier_eq 1), second⟩⟩
  · intro x member
    obtain ⟨t, member⟩ := Set.mem_iUnion.mp member
    obtain ⟨same, on_triangle⟩ := Set.mem_iUnion.mp member
    rw [← same]
    exact graph.triangle_subset_face small_faces t on_triangle

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
