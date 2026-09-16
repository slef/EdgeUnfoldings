import SixVertexUnfolding.Geometry.FourRaySideIntersections
import SixVertexUnfolding.Geometry.VertexFigureSectors
import SixVertexUnfolding.Geometry.OctahedralFanPointAngles

/-! Intersections of the actual spatial sectors, before any unfolding. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set OctahedralTriangles

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include small_faces in
/-- Two different sectors can share a nonpole point only on a common radial ray. -/
theorem common_sector_ray (pole : Fin 6) (i j : Fin 4) (different : i ≠ j)
    (x : Space) (first : x ∈ graph.triangle (fanTriangle pole i))
    (second : x ∈ graph.triangle (fanTriangle pole j)) (nonpole : x ≠ graph.vertex pole) :
    (j = i + 1 ∧ ∃ t : ℝ, 0 < t ∧
      x = t • ((graph.vertex (fanNeighbor pole (i + 1)) : Space) - graph.vertex pole) + graph.vertex pole) ∨
    (i = j + 1 ∧ ∃ t : ℝ, 0 < t ∧
      x = t • ((graph.vertex (fanNeighbor pole i) : Space) - graph.vertex pole) + graph.vertex pole) := by
  obtain ⟨normal, strict⟩ := P.vertex_strict_support (graph.vertex pole).property
  let figure : P.VertexFigure (graph.vertex pole) := ⟨normal, strict⟩
  have gaps (k : Fin 4) : 0 < figure.gap (graph.vertex (fanNeighbor pole k)) :=
    figure.gap_pos (graph.vertex (fanNeighbor pole k)).property (graph.fan_neighbor_distinct pole k)
  have member (k : Fin 4) (hx : x ∈ graph.triangle (fanTriangle pole k)) :
      x ∈ convexHull ℝ ({(graph.vertex pole : Space), (graph.vertex (fanNeighbor pole k) : Space),
        (graph.vertex (fanNeighbor pole (k + 1)) : Space)} : Set Space) := by
    simpa only [triangle, fanTriangle_vertices, graph.labeledHull_triple] using hx
  have projected (k : Fin 4) (hx : x ∈ graph.triangle (fanTriangle pole k)) :
      figure.direction x ∈ segment ℝ ((graph.vertexFan pole figure small_faces).ray k)
        ((graph.vertexFan pole figure small_faces).ray (k + 1)) :=
    figure.sector_direction_in_side _ _ (gaps k) (gaps (k + 1)) x (member k hx) nonpole
  have positive := figure.sector_gap_positive _ _ (gaps i) (gaps (i + 1)) x (member i first) nonpole
  rcases (graph.vertexFan pole figure small_faces).common_side_point i j different
      (projected i first) (projected j second) with h | h
  · exact Or.inl ⟨h.1, figure.equal_direction_ray _ x (gaps (i + 1)) positive h.2⟩
  · exact Or.inr ⟨h.1, figure.equal_direction_ray _ x (gaps i) positive h.2⟩

/-- Moving positively along a ray does not change its ordinary angle. -/
theorem fanOffset_on_ray (pole : Fin 6) (i j : Fin 4) (t : ℝ) (positive : 0 < t) :
    graph.fanOffset pole i
      (t • ((graph.vertex (fanNeighbor pole j) : Space) - graph.vertex pole) + graph.vertex pole) =
    EuclideanGeometry.angle (graph.vertex (fanNeighbor pole i) : Space) (graph.vertex pole)
      (graph.vertex (fanNeighbor pole j)) := by
  unfold fanOffset EuclideanGeometry.angle
  simp only [vsub_eq_sub, add_sub_cancel_right]
  exact InnerProductGeometry.angle_smul_right_of_pos _ _ positive

include small_faces in
/-- At a common radial edge the preceding offset is its full sector angle,
and the following offset is zero. -/
theorem adjacent_sector_offsets (pole : Fin 6) (i : Fin 4) (x : Space)
    (first : x ∈ graph.triangle (fanTriangle pole i))
    (second : x ∈ graph.triangle (fanTriangle pole (i + 1)))
    (nonpole : x ≠ graph.vertex pole) :
    graph.fanOffset pole i x = graph.fanAngle pole i ∧ graph.fanOffset pole (i + 1) x = 0 := by
  have distinct : i ≠ i + 1 := (by decide : ∀ i : Fin 4, i ≠ i + 1) i
  rcases graph.common_sector_ray small_faces pole i (i + 1) distinct x first second nonpole with h | h
  · obtain ⟨t, positive, rfl⟩ := h.2
    rw [graph.fanOffset_on_ray pole i (i + 1) t positive,
      graph.fanOffset_on_ray pole (i + 1) (i + 1) t positive]
    exact ⟨rfl, EuclideanGeometry.angle_self_of_ne (graph.fan_neighbor_distinct pole (i + 1))⟩
  · have impossible : ∀ i : Fin 4, i ≠ i + 1 + 1 := by decide
    exact False.elim (impossible i h.1)

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
