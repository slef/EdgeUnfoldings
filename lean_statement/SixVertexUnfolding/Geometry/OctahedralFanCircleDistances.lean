import SixVertexUnfolding.Geometry.OctahedralFanCircle
import SixVertexUnfolding.Geometry.TriangleAngleComparison

/-! Within one actual sector the circle coordinate changes by at most
the ordinary spatial angle. This is the local metric comparison. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set OctahedralTriangles Real

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include small_faces in
/-- Ordered offsets in a single sector differ by their ordinary spatial angle. -/
theorem fanOffset_difference_of_le (pole : Fin 6) (i : Fin 4) (x y : Space)
    (hx : x ∈ graph.triangle (fanTriangle pole i)) (hy : y ∈ graph.triangle (fanTriangle pole i))
    (x_ne : x ≠ graph.vertex pole) (y_ne : y ≠ graph.vertex pole)
    (ordered : graph.fanOffset pole i x ≤ graph.fanOffset pole i y) :
    EuclideanGeometry.angle x (graph.vertex pole) y = graph.fanOffset pole i y - graph.fanOffset pole i x := by
  let fan := Classical.choice (graph.exists_fan_development small_faces pole i)
  have cx := fan.point_polar_coordinates 0 x (by simpa only [add_zero] using hx) x_ne
  have cy := fan.point_polar_coordinates 0 y (by simpa only [add_zero] using hy) y_ne
  simp only [add_zero, show graph.openingAngle pole i (Fin.castSucc 0) = 0 from rfl, zero_add] at cx cy
  let F := graph.triangleFace small_faces (fanTriangle pole i)
  have xF : x ∈ F.val := graph.triangle_subset_face small_faces _ hx
  have yF : y ∈ F.val := graph.triangle_subset_face small_faces _ hy
  have poleF : (graph.vertex pole : Space) ∈ F.val := graph.fan_sector_on_face pole small_faces i _ (by simp)
  have rigid (a b : Space) (ha : a ∈ F.val) (hb : b ∈ F.val) :
      dist (fan.place 0 a) (fan.place 0 b) = dist a b :=
    fan.rigid 0 a (by simpa only [add_zero] using ha) b (by simpa only [add_zero] using hb)
  have measured := triangle_angle_of_distances (graph.vertex pole) x y
    (fan.place 0 (graph.vertex pole)) (fan.place 0 x) (fan.place 0 y)
    (rigid _ _ poleF xF) (rigid _ _ poleF yF) (rigid _ _ xF yF)
  rw [fan.at_pole, cx.2.2, cy.2.2] at measured
  rw [← measured]
  exact radial_angle _ _ _ _ (dist_pos.mpr x_ne.symm) (dist_pos.mpr y_ne.symm)
    (sub_nonneg.mpr ordered) (by linarith [graph.fanAngle_lt_pi pole i, cx.1, cy.2.1])

include small_faces in
/-- The absolute offset difference is precisely the ordinary angle in that sector. -/
theorem fanOffset_difference (pole : Fin 6) (i : Fin 4) (x y : Space)
    (hx : x ∈ graph.triangle (fanTriangle pole i)) (hy : y ∈ graph.triangle (fanTriangle pole i))
    (x_ne : x ≠ graph.vertex pole) (y_ne : y ≠ graph.vertex pole) :
    |graph.fanOffset pole i x - graph.fanOffset pole i y| =
      EuclideanGeometry.angle x (graph.vertex pole) y := by
  rcases le_total (graph.fanOffset pole i x) (graph.fanOffset pole i y) with h | h
  · rw [graph.fanOffset_difference_of_le small_faces pole i x y hx hy x_ne y_ne h,
      abs_of_nonpos (sub_nonpos.mpr h), neg_sub]
  · rw [EuclideanGeometry.angle_comm,
      graph.fanOffset_difference_of_le small_faces pole i y x hy hx y_ne x_ne h,
      abs_of_nonneg (sub_nonneg.mpr h)]

include small_faces in
/-- Passing to the angular circle can only shorten the same-sector angular distance. -/
theorem fanCircleMap_dist_le_angle (pole : Fin 6) (i : Fin 4) (x y : Space)
    (hx : x ∈ graph.triangle (fanTriangle pole i)) (hy : y ∈ graph.triangle (fanTriangle pole i))
    (x_ne : x ≠ graph.vertex pole) (y_ne : y ≠ graph.vertex pole) :
    dist (graph.fanCircleMap pole x) (graph.fanCircleMap pole y) ≤
      EuclideanGeometry.angle x (graph.vertex pole) y := by
  rw [graph.fanCircleMap_on_sector small_faces pole i x hx x_ne,
    graph.fanCircleMap_on_sector small_faces pole i y hy y_ne]
  have quotient : ∀ a b : ℝ, dist (a : AddCircle (graph.totalAngleAt pole)) (b : AddCircle _) ≤ |a - b| := by
    intro a b
    rw [dist_eq_norm, ← AddCircle.coe_sub]
    exact QuotientAddGroup.norm_mk_le_norm
  have bound := quotient (graph.openingAngle pole 0 i.castSucc + graph.fanOffset pole i x)
    (graph.openingAngle pole 0 i.castSucc + graph.fanOffset pole i y)
  simp only [add_sub_add_left_eq_sub] at bound
  exact bound.trans_eq (graph.fanOffset_difference small_faces pole i x y hx hy x_ne y_ne)

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
