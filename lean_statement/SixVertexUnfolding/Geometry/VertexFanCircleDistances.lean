import SixVertexUnfolding.Geometry.VertexFanCircle
import SixVertexUnfolding.Geometry.TriangleAngleComparison

/-! Within one actual sector the circle coordinate changes by at most
the ordinary spatial angle. This is the local metric comparison. -/

namespace SixVertexUnfolding.ConvexPolyhedron.VertexFaceFan

open Set Real

variable {P : ConvexPolyhedron} {pole : P.Vertex} {n : ℕ} [NeZero n]
  (fan : P.VertexFaceFan pole n)
    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4)

/-- Ordered offsets in a single sector differ by their ordinary spatial angle. -/
theorem offset_difference_of_le (i : Fin n) (x y : Space)
    (hx : x ∈ fan.triangle i) (hy : y ∈ fan.triangle i)
    (x_ne : x ≠ pole) (y_ne : y ≠ pole)
    (ordered : fan.offset i x ≤ fan.offset i y) :
    EuclideanGeometry.angle x (pole) y = fan.offset i y - fan.offset i x := by
  let net := Classical.choice (fan.exists_development i)
  have cx := net.point_polar_coordinates 0 x (by simpa only [add_zero] using hx) x_ne
  have cy := net.point_polar_coordinates 0 y (by simpa only [add_zero] using hy) y_ne
  simp only [add_zero, Fin.castSucc_zero, fan.openingAngle_zero, zero_add] at cx cy
  let F := fan.face i
  have xF : x ∈ F.val := fan.triangle_subset_face _ hx
  have yF : y ∈ F.val := fan.triangle_subset_face _ hy
  have poleF : (pole : Space) ∈ F.val := fan.pole_mem i
  have rigid (a b : Space) (ha : a ∈ F.val) (hb : b ∈ F.val) :
      dist (net.place 0 a) (net.place 0 b) = dist a b :=
    net.rigid 0 a (by simpa only [add_zero] using ha) b (by simpa only [add_zero] using hb)
  have measured := triangle_angle_of_distances (pole) x y
    (net.place 0 (pole)) (net.place 0 x) (net.place 0 y)
    (rigid _ _ poleF xF) (rigid _ _ poleF yF) (rigid _ _ xF yF)
  rw [net.at_pole, cx.2.2, cy.2.2] at measured
  rw [← measured]
  exact radial_angle _ _ _ _ (dist_pos.mpr x_ne.symm) (dist_pos.mpr y_ne.symm)
    (sub_nonneg.mpr ordered) (by linarith [fan.sectorAngle_lt_pi i, cx.1, cy.2.1])

/-- The absolute offset difference is precisely the ordinary angle in that sector. -/
theorem offset_difference (i : Fin n) (x y : Space)
    (hx : x ∈ fan.triangle i) (hy : y ∈ fan.triangle i)
    (x_ne : x ≠ pole) (y_ne : y ≠ pole) :
    |fan.offset i x - fan.offset i y| =
      EuclideanGeometry.angle x (pole) y := by
  rcases le_total (fan.offset i x) (fan.offset i y) with h | h
  · rw [fan.offset_difference_of_le i x y hx hy x_ne y_ne h,
      abs_of_nonpos (sub_nonpos.mpr h), neg_sub]
  · rw [EuclideanGeometry.angle_comm,
      fan.offset_difference_of_le i y x hy hx y_ne x_ne h,
      abs_of_nonneg (sub_nonneg.mpr h)]

include small_faces in
/-- Passing to the angular circle can only shorten the same-sector angular distance. -/
theorem fanCircleMap_dist_le_angle (i : Fin n) (x y : Space)
    (hx : x ∈ fan.triangle i) (hy : y ∈ fan.triangle i)
    (x_ne : x ≠ pole) (y_ne : y ≠ pole) :
    dist (fan.fanCircleMap x) (fan.fanCircleMap y) ≤
      EuclideanGeometry.angle x (pole) y := by
  rw [fan.fanCircleMap_on_sector small_faces i x hx x_ne,
    fan.fanCircleMap_on_sector small_faces i y hy y_ne]
  have quotient : ∀ a b : ℝ, dist (a : AddCircle (fan.totalAngle)) (b : AddCircle _) ≤ |a - b| := by
    intro a b
    rw [dist_eq_norm, ← AddCircle.coe_sub]
    exact QuotientAddGroup.norm_mk_le_norm
  have bound := quotient (fan.openingAngle 0 i.castSucc + fan.offset i x)
    (fan.openingAngle 0 i.castSucc + fan.offset i y)
  simp only [add_sub_add_left_eq_sub] at bound
  exact bound.trans_eq (fan.offset_difference i x y hx hy x_ne y_ne)

end SixVertexUnfolding.ConvexPolyhedron.VertexFaceFan
