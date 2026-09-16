import SixVertexUnfolding.Geometry.OctahedralFanBoundary
import SixVertexUnfolding.Geometry.JoinedTriangles

/-! The closed triangles of an opened vertex fan meet exactly along their
shared radial edges, or at the pole alone. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set Real

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)

/-- Each opened triangle has positive oriented area. -/
theorem openingTriangle_area_pos (pole : Fin 6) (slit i : Fin 4) :
    0 < det (graph.openingPoint pole slit i.castSucc) (graph.openingPoint pole slit i.succ) := by
  change 0 < det (_ • direction _) (_ • direction _)
  rw [det_smul_left, det_smul_right, direction_det, graph.openingAngle_step]
  exact mul_pos (graph.opening_radius_pos _ _ _)
    (mul_pos (graph.opening_radius_pos _ _ _)
      (sin_pos_of_pos_of_lt_pi (graph.fanAngle_pos _ _) (graph.fanAngle_lt_pi _ _)))

/-- Adjacent closed sectors meet only on their common radial segment. -/
theorem openingTriangles_adjacent_intersection (pole : Fin 6) (slit : Fin 4) (i : Fin 3) :
    graph.openingTriangle pole slit i.castSucc ∩ graph.openingTriangle pole slit i.succ =
      segment ℝ 0 (graph.openingPoint pole slit i.castSucc.succ) := by
  have first := graph.openingTriangle_area_pos pole slit i.castSucc
  have second := graph.openingTriangle_area_pos pole slit i.succ
  have opposite :
      det (graph.openingPoint pole slit i.castSucc.succ - 0)
          (graph.openingPoint pole slit i.castSucc.castSucc - 0) *
        det (graph.openingPoint pole slit i.castSucc.succ - 0)
          (graph.openingPoint pole slit i.succ.succ - 0) < 0 := by
    simp only [sub_zero]
    rw [det_swap (graph.openingPoint pole slit i.castSucc.succ)]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos first) second
  have intersection := opposite_triangles_intersection 0
    (graph.openingPoint pole slit i.castSucc.succ)
    (graph.openingPoint pole slit i.castSucc.castSucc)
    (graph.openingPoint pole slit i.succ.succ) opposite
  change convexHull ℝ ({0, graph.openingPoint pole slit i.castSucc.castSucc,
      graph.openingPoint pole slit i.castSucc.succ} : Set Plane) ∩
    convexHull ℝ ({0, graph.openingPoint pole slit i.castSucc.succ,
      graph.openingPoint pole slit i.succ.succ} : Set Plane) = _
  rw [show ({0, graph.openingPoint pole slit i.castSucc.castSucc,
      graph.openingPoint pole slit i.castSucc.succ} : Set Plane) =
    {0, graph.openingPoint pole slit i.castSucc.succ,
      graph.openingPoint pole slit i.castSucc.castSucc} by
        ext x; simp only [mem_insert_iff, mem_singleton_iff]; tauto]
  exact intersection

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
