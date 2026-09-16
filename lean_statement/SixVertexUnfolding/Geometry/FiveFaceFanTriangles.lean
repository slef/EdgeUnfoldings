import SixVertexUnfolding.Geometry.FiveFaceFanCoordinates
import SixVertexUnfolding.Geometry.StrictPlanarSectors
import SixVertexUnfolding.Geometry.JoinedTriangles

/-! Contacts of the five opened triangles: adjacent ones share a radial
edge; nonadjacent ones meet only at the common vertex. -/

namespace SixVertexUnfolding.ConvexPolyhedron.FiveFaceFan

open Set Real

variable {P : ConvexPolyhedron} {pole : P.Vertex} (fan : P.FiveFaceFan pole)

def openingTriangle (slit i : Fin 5) : Set Plane :=
  convexHull ℝ ({0, fan.openingPoint slit i.castSucc, fan.openingPoint slit i.succ} : Set Plane)

theorem openingTriangle_area_pos (slit i : Fin 5) :
    0 < det (fan.openingPoint slit i.castSucc) (fan.openingPoint slit i.succ) := by
  change 0 < det (_ • direction _) (_ • direction _)
  rw [det_smul_left, det_smul_right, direction_det, fan.openingAngle_step]
  exact mul_pos (fan.opening_radius_pos _ _)
    (mul_pos (fan.opening_radius_pos _ _)
      (sin_pos_of_pos_of_lt_pi (fan.sectorAngle_pos _) (fan.sectorAngle_lt_pi _)))

theorem openingTriangles_meet_only_at_zero (slit i j : Fin 5)
    (intervening : i.val + 1 < j.val) (x : Plane)
    (left : x ∈ fan.openingTriangle slit i) (right : x ∈ fan.openingTriangle slit j) : x = 0 := by
  have mono := (fan.openingAngle_strictMono slit).monotone
  apply radial_triangles_meet_only_at_zero (fan.opening_radius_pos slit i.castSucc)
    (fan.opening_radius_pos slit i.succ) (fan.opening_radius_pos slit j.castSucc)
    (fan.opening_radius_pos slit j.succ)
    (mono (by change i.val ≤ i.val + 1; omega))
    (fan.openingAngle_strictMono slit (show i.succ < j.castSucc from intervening))
    (mono (by change j.val ≤ j.val + 1; omega))
    (by rw [fan.openingAngle_step]; exact fan.sectorAngle_lt_pi _)
    (by rw [fan.openingAngle_step]; exact fan.sectorAngle_lt_pi _) _ x left right
  have lower := fan.openingAngle_nonneg slit i.castSucc
  have upper := fan.openingAngle_le_total slit j.succ
  have total := fan.totalAngle_lt_two_pi
  linarith

theorem openingTriangles_adjacent_intersection (slit : Fin 5) (i : Fin 4) :
    fan.openingTriangle slit i.castSucc ∩ fan.openingTriangle slit i.succ =
      segment ℝ 0 (fan.openingPoint slit i.castSucc.succ) := by
  have first := fan.openingTriangle_area_pos slit i.castSucc
  have second := fan.openingTriangle_area_pos slit i.succ
  have opposite :
      det (fan.openingPoint slit i.castSucc.succ - 0)
          (fan.openingPoint slit i.castSucc.castSucc - 0) *
        det (fan.openingPoint slit i.castSucc.succ - 0)
          (fan.openingPoint slit i.succ.succ - 0) < 0 := by
    simp only [sub_zero]
    rw [det_swap (fan.openingPoint slit i.castSucc.succ)]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos first) second
  have intersection := opposite_triangles_intersection 0
    (fan.openingPoint slit i.castSucc.succ)
    (fan.openingPoint slit i.castSucc.castSucc)
    (fan.openingPoint slit i.succ.succ) opposite
  change convexHull ℝ ({0, fan.openingPoint slit i.castSucc.castSucc,
      fan.openingPoint slit i.castSucc.succ} : Set Plane) ∩
    convexHull ℝ ({0, fan.openingPoint slit i.castSucc.succ,
      fan.openingPoint slit i.succ.succ} : Set Plane) = _
  rw [show ({0, fan.openingPoint slit i.castSucc.castSucc,
      fan.openingPoint slit i.castSucc.succ} : Set Plane) =
    {0, fan.openingPoint slit i.castSucc.succ,
      fan.openingPoint slit i.castSucc.castSucc} by
        ext x; simp only [mem_insert_iff, mem_singleton_iff]; tauto]
  exact intersection

end SixVertexUnfolding.ConvexPolyhedron.FiveFaceFan
