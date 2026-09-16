import SixVertexUnfolding.Geometry.UniversalVertexNeighborhood
import SixVertexUnfolding.Geometry.FiveRayPerimeter

/-! Transfer the strict five-ray angle bound to the actual original faces
around a universal vertex of a six-vertex convex polyhedron. -/

namespace SixVertexUnfolding.ConvexPolyhedron

open Set InnerProductGeometry

/-- All five incident faces, in their actual cyclic order, have total
angle strictly below a full turn at the universal vertex. -/
theorem universal_vertex_angle_deficit (P : ConvexPolyhedron) (size : P.vertices.card = 6)
    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4)
    (source : P.Vertex) (universal : ∀ v : P.Vertex, v ≠ source → P.edgeGraph.Adj source v) :
    ∃ order : Fin 5 ≃ {v : P.Vertex // v ≠ source}, ∃ faces : Fin 5 → P.Face,
      (∀ i : Fin 5, (faces i).val ∩ (P.vertices : Set Space) =
        {(source : Space), ((order i).val : Space), ((order (i + 1)).val : Space)}) ∧
      (∀ F : P.Face, (source : Space) ∈ F.val ↔ F ∈ range faces) ∧
      (∑ i : Fin 5, angle (((order i).val : Space) - source)
        (((order (i + 1)).val : Space) - source)) < 2 * Real.pi := by
  obtain ⟨normal, strict⟩ := P.vertex_strict_support source.property
  let figure : P.VertexFigure source := ⟨normal, strict⟩
  obtain ⟨fan, order, faces, directions, vertices, covers, _⟩ :=
    P.universal_vertex_five_ray_figure size small_faces source universal figure
  refine ⟨order, faces, vertices, covers, ?_⟩
  have angles (i : Fin 5) : angle (fan.ray i) (fan.ray (i + 1)) =
      angle (((order i).val : Space) - source) (((order (i + 1)).val : Space) - source) := by
    rw [directions i, directions (i + 1)]
    exact figure.direction_angle (order i).val (order (i + 1)).val
      (order i).property (order (i + 1)).property
  have bound := fan.sum_angles_lt_two_pi
  simpa only [angles] using bound

end SixVertexUnfolding.ConvexPolyhedron
