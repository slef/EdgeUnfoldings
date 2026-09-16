import SixVertexUnfolding.Geometry.BisectorBaseTriangles
import SixVertexUnfolding.Geometry.HingeDeterminant
import SixVertexUnfolding.Geometry.PlaneOrientation
import SixVertexUnfolding.Geometry.JoinedTriangles

/-! Equal distances to the two base endpoints place distinct planar
source copies strictly on opposite sides. Their triangles meet exactly
along the common base. -/

namespace SixVertexUnfolding

open Set

/-- Distinct sites with equal distances to a base lie strictly on opposite sides of its line. -/
theorem bisector_sites_opposite (p q u v : Plane) (different : p ≠ q) (base : u ≠ v)
    (left : dist p u = dist q u) (right : dist p v = dist q v) :
    det (v - u) (p - u) * det (v - u) (q - u) < 0 := by
  have strict : inner ℝ (hingeSideVector u v p) (hingeSideVector u v q) < 0 := by
    apply lt_of_not_ge
    intro same_side
    exact different (point_eq_of_hinge_distances u v p q base
      (by simpa only [dist_comm] using left) (by simpa only [dist_comm] using right) same_side)
  have weak := (oppositeHingeSides_iff_det u v p q base).mp strict.le
  have first : ¬ Collinear ℝ ({u, v, p} : Set Plane) := by
    rw [show ({u, v, p} : Set Plane) = {p, u, v} by ext x; simp only [mem_insert_iff, mem_singleton_iff]; tauto]
    exact bisector_base_noncollinear p q u v different base left right
  have second : ¬ Collinear ℝ ({u, v, q} : Set Plane) := by
    rw [show ({u, v, q} : Set Plane) = {q, u, v} by ext x; simp only [mem_insert_iff, mem_singleton_iff]; tauto]
    exact bisector_base_noncollinear q p u v different.symm base left.symm right.symm
  exact lt_of_le_of_ne weak (mul_ne_zero (det_ne_zero_of_noncollinear u v p first)
    (det_ne_zero_of_noncollinear u v q second))

/-- The two metric triangles form a kite with no overlap outside their common base. -/
theorem bisector_kite_intersection (p q u v : Plane) (different : p ≠ q) (base : u ≠ v)
    (left : dist p u = dist q u) (right : dist p v = dist q v) :
    convexHull ℝ ({u, v, p} : Set Plane) ∩ convexHull ℝ ({u, v, q} : Set Plane) = segment ℝ u v :=
  opposite_triangles_intersection u v p q (bisector_sites_opposite p q u v different base left right)

end SixVertexUnfolding
