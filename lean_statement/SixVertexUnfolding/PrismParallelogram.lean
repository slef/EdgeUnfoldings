import SixVertexUnfolding.PrismFlower
import SixVertexUnfolding.Geometry.ParallelPetals

/-! The prism flower is complete whenever its selected quadrilateral base is a parallelogram. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

variable {P : ConvexPolyhedron}

/-- A prism with this parallelogram facet has an original-edge unfolding, without assumptions on its triangular bases. -/
theorem hasEdgeUnfolding_of_prism_parallelogram (graph : P.SixVertexGraph)
    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4)
    (kind : graph.kind = .prism)
    (parallelogram : (graph.vertex 0 : Space) + graph.vertex 1 =
      (graph.vertex 3 : Space) + graph.vertex 4) : P.HasEdgeUnfolding := by
  obtain ⟨net⟩ := (graph.prismDome small_faces kind).exists_development
  have inside (i : Fin 5) (v : Fin 6) (member : v ∈ PrismFlower.labels i) :
      (graph.vertex v : Space) ∈ (graph.prismFace small_faces kind i).val := by
    rw [← Face.mem_vertexLabels, graph.prismFace_labels small_faces kind]
    exact member
  have side (i : Fin 5) (nonzero : i ≠ 0) :
      graph.prismFace small_faces kind i ≠ (graph.prismDome small_faces kind).base :=
    fun same => nonzero (graph.prismFace_injective small_faces kind same)
  apply graph.prism_unfolding_of_two_pairs small_faces kind net
  · have separated := net.parallel_petals_disjoint
      (graph.prismFace small_faces kind 1) (graph.prismFace small_faces kind 3)
      (side 1 (by decide)) (side 3 (by decide))
      (graph.vertex 0) (graph.vertex 3) (graph.vertex 1) (graph.vertex 4)
      (graph.vertex.injective.ne (by decide)) (graph.vertex.injective.ne (by decide))
      (graph.vertex.injective.ne (by decide)) (graph.vertex.injective.ne (by decide))
      (inside 0 0 (by decide)) (inside 0 3 (by decide))
      (inside 0 1 (by decide)) (inside 0 4 (by decide))
      (inside 1 0 (by decide)) (inside 1 3 (by decide))
      (inside 3 1 (by decide)) (inside 3 4 (by decide)) (-1) (by
        linear_combination (norm := module) -parallelogram)
    exact separated.mono interior_subset interior_subset
  · have separated := net.parallel_petals_disjoint
      (graph.prismFace small_faces kind 2) (graph.prismFace small_faces kind 4)
      (side 2 (by decide)) (side 4 (by decide))
      (graph.vertex 1) (graph.vertex 3) (graph.vertex 0) (graph.vertex 4)
      (graph.vertex.injective.ne (by decide)) (graph.vertex.injective.ne (by decide))
      (graph.vertex.injective.ne (by decide)) (graph.vertex.injective.ne (by decide))
      (inside 0 1 (by decide)) (inside 0 3 (by decide))
      (inside 0 0 (by decide)) (inside 0 4 (by decide))
      (inside 2 1 (by decide)) (inside 2 3 (by decide))
      (inside 4 0 (by decide)) (inside 4 4 (by decide)) (-1) (by
        linear_combination (norm := module) -parallelogram)
    exact separated.mono interior_subset interior_subset

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
