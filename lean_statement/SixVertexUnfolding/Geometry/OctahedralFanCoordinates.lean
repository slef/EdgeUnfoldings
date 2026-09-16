import SixVertexUnfolding.Geometry.OctahedralClosedLink
import SixVertexUnfolding.Geometry.PlanarDirections

/-! Explicit polar coordinates for the four fan triangles, opened at any chosen equator ray. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open OctahedralTriangles EuclideanGeometry Real

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)

/-- The actual angle of one fan sector at its pole. -/
noncomputable def fanAngle (pole : Fin 6) (i : Fin 4) : ℝ :=
  angle (graph.vertex (fanNeighbor pole i) : Space) (graph.vertex pole) (graph.vertex (fanNeighbor pole (i + 1)))

theorem fan_triangle_noncollinear (pole : Fin 6) (i : Fin 4) :
    ¬ Collinear ℝ ({(graph.vertex (fanNeighbor pole i) : Space), (graph.vertex pole : Space),
      (graph.vertex (fanNeighbor pole (i + 1)) : Space)} : Set Space) := by
  apply P.no_three_collinear_vertices (graph.vertex (fanNeighbor pole i)).property
    (graph.vertex pole).property (graph.vertex (fanNeighbor pole (i + 1))).property
  · exact fun same => fanNeighbor_ne_source pole i (graph.vertex.injective (Subtype.ext same))
  · exact fun same => (fanNeighbor_injective pole).ne ((by decide : ∀ i : Fin 4, i ≠ i + 1) i)
      (graph.vertex.injective (Subtype.ext same))
  · exact fun same => fanNeighbor_ne_source pole (i + 1) (graph.vertex.injective (Subtype.ext same)).symm

theorem fanAngle_pos (pole : Fin 6) (i : Fin 4) : 0 < graph.fanAngle pole i :=
  angle_pos_of_not_collinear (graph.fan_triangle_noncollinear pole i)

theorem fanAngle_lt_pi (pole : Fin 6) (i : Fin 4) : graph.fanAngle pole i < π :=
  angle_lt_pi_of_not_collinear (graph.fan_triangle_noncollinear pole i)

theorem sum_fanAngle (pole : Fin 6) : (∑ i : Fin 4, graph.fanAngle pole i) = graph.totalAngleAt pole :=
  (graph.totalAngleAt_eq_fan_angles pole).symm

/-- The slit endpoint occurs twice, at the beginning and end of the opened fan. -/
def openingVertex (pole : Fin 6) (slit : Fin 4) : Fin 5 → Fin 6 :=
  ![fanNeighbor pole slit, fanNeighbor pole (slit + 1), fanNeighbor pole (slit + 2),
    fanNeighbor pole (slit + 3), fanNeighbor pole slit]

/-- The five cumulative directions of the four consecutive fan sectors. -/
noncomputable def openingAngle (pole : Fin 6) (slit : Fin 4) : Fin 5 → ℝ :=
  ![0, graph.fanAngle pole slit,
    graph.fanAngle pole slit + graph.fanAngle pole (slit + 1),
    graph.fanAngle pole slit + graph.fanAngle pole (slit + 1) + graph.fanAngle pole (slit + 2),
    graph.fanAngle pole slit + graph.fanAngle pole (slit + 1) + graph.fanAngle pole (slit + 2) +
      graph.fanAngle pole (slit + 3)]

theorem openingVertex_start : ∀ pole slit i,
    openingVertex pole slit (Fin.castSucc i) = fanNeighbor pole (slit + i) := by decide

theorem openingVertex_end : ∀ pole slit i,
    openingVertex pole slit (Fin.succ i) = fanNeighbor pole ((slit + i) + 1) := by decide

theorem openingAngle_step (pole : Fin 6) (slit i : Fin 4) :
    graph.openingAngle pole slit i.succ - graph.openingAngle pole slit i.castSucc = graph.fanAngle pole (slit + i) := by
  fin_cases i <;> simp [openingAngle]

theorem openingAngle_strictMono (pole : Fin 6) (slit : Fin 4) : StrictMono (graph.openingAngle pole slit) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  have positive := graph.fanAngle_pos pole (slit + i)
  have step := graph.openingAngle_step pole slit i
  linarith

theorem openingAngle_last (pole : Fin 6) (slit : Fin 4) : graph.openingAngle pole slit 4 = graph.totalAngleAt pole := by
  rw [← graph.sum_fanAngle]
  fin_cases slit <;> simp [openingAngle, Fin.sum_univ_four] <;> ring

/-- The actual radial lengths, placed at those cumulative directions in the plane. -/
noncomputable def openingPoint (pole : Fin 6) (slit : Fin 4) (i : Fin 5) : Plane :=
  dist (graph.vertex pole : Space) (graph.vertex (openingVertex pole slit i)) • direction (graph.openingAngle pole slit i)

theorem openingPoint_radius (pole : Fin 6) (slit : Fin 4) (i : Fin 5) :
    dist 0 (graph.openingPoint pole slit i) = dist (graph.vertex pole : Space) (graph.vertex (openingVertex pole slit i)) :=
  polar_radius _ _ dist_nonneg

/-- Each opened fan base has precisely its original spatial edge length. -/
theorem openingPoint_base (pole : Fin 6) (slit i : Fin 4) :
    dist (graph.openingPoint pole slit i.castSucc) (graph.openingPoint pole slit i.succ) =
      dist (graph.vertex (fanNeighbor pole (slit + i)) : Space) (graph.vertex (fanNeighbor pole ((slit + i) + 1))) := by
  apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
  rw [openingPoint, openingPoint, polar_distance_sq, graph.openingAngle_step,
    openingVertex_start, openingVertex_end]
  have cosine_law := law_cos (graph.vertex (fanNeighbor pole (slit + i)) : Space) (graph.vertex pole)
    (graph.vertex (fanNeighbor pole ((slit + i) + 1)))
  simp only [← sq, dist_comm (graph.vertex (fanNeighbor pole (slit + i)) : Space) (graph.vertex pole),
    dist_comm (graph.vertex (fanNeighbor pole ((slit + i) + 1)) : Space) (graph.vertex pole)] at cosine_law
  exact cosine_law.symm

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
