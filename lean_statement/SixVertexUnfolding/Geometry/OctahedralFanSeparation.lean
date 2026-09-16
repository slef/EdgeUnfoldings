import SixVertexUnfolding.Geometry.OctahedralFanCoordinates
import SixVertexUnfolding.Geometry.PlanarSectors

/-! All six pairs of the four opened fan triangles have disjoint interiors. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Real

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)

/-- A closed triangle of the opened four-triangle fan. -/
def openingTriangle (pole : Fin 6) (slit i : Fin 4) : Set Plane :=
  convexHull ℝ ({0, graph.openingPoint pole slit i.castSucc, graph.openingPoint pole slit i.succ} : Set Plane)

theorem openingAngle_nonneg (pole : Fin 6) (slit : Fin 4) (i : Fin 5) : 0 ≤ graph.openingAngle pole slit i :=
  (graph.openingAngle_strictMono pole slit).monotone (show (0 : Fin 5) ≤ i from Fin.zero_le i)

theorem openingAngle_le_total (pole : Fin 6) (slit : Fin 4) (i : Fin 5) :
    graph.openingAngle pole slit i ≤ graph.totalAngleAt pole := by
  rw [← graph.openingAngle_last pole slit]
  exact (graph.openingAngle_strictMono pole slit).monotone (by omega : i ≤ (4 : Fin 5))

variable (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include small_faces in
/-- Earlier and later fan sectors are separated by a line through the common pole. -/
theorem openingTriangles_disjoint_of_lt (pole : Fin 6) (slit i j : Fin 4) (ordered : i < j) :
    Disjoint (interior (graph.openingTriangle pole slit i)) (interior (graph.openingTriangle pole slit j)) := by
  have mono := (graph.openingAngle_strictMono pole slit).monotone
  have first_width := graph.openingAngle_step pole slit i
  have second_width := graph.openingAngle_step pole slit j
  change Disjoint (interior (radialTriangle _ _ _ _)) (interior (radialTriangle _ _ _ _))
  apply radial_triangles_disjoint dist_nonneg dist_nonneg dist_nonneg dist_nonneg
  · exact mono (by change i.val ≤ i.val + 1; omega)
  · exact mono (by change i.val + 1 ≤ j.val; exact Nat.succ_le_of_lt ordered)
  · exact mono (by change j.val ≤ j.val + 1; omega)
  · linarith [graph.fanAngle_lt_pi pole (slit + i)]
  · linarith [graph.fanAngle_lt_pi pole (slit + j)]
  · have lower := graph.openingAngle_nonneg pole slit i.castSucc
    have upper := graph.openingAngle_le_total pole slit j.succ
    have total := graph.totalAngleAt_lt_two_pi small_faces pole
    linarith

include small_faces in
/-- The whole blue fan has no triangle-interior overlaps, at every possible slit. -/
theorem openingTriangles_disjoint (pole : Fin 6) (slit i j : Fin 4) (different : i ≠ j) :
    Disjoint (interior (graph.openingTriangle pole slit i)) (interior (graph.openingTriangle pole slit j)) := by
  rcases lt_or_gt_of_ne different with before | after
  · exact graph.openingTriangles_disjoint_of_lt small_faces pole slit i j before
  · exact (graph.openingTriangles_disjoint_of_lt small_faces pole slit j i after).symm

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
