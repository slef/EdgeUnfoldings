import SixVertexUnfolding.Geometry.FiveFaceFanDevelopment
import SixVertexUnfolding.Geometry.RadialTriangleCorners
import SixVertexUnfolding.Geometry.TriangleAngles

/-! Polar coordinates of original surface points, with offsets independent of the slit. -/

namespace SixVertexUnfolding.ConvexPolyhedron.FiveFaceFan

open Set Real

variable {P : ConvexPolyhedron} {pole : P.Vertex} (fan : P.FiveFaceFan pole)

noncomputable def offset (sector : Fin 5) (x : Space) : ℝ :=
  EuclideanGeometry.angle (fan.neighbor sector : Space) pole x

namespace Development

variable {fan} {slit : Fin 5} (net : fan.Development slit)

theorem point_polar_coordinates (i : Fin 5) (x : Space)
    (member : x ∈ fan.triangle (slit + i)) (nonpole : x ≠ pole) :
    0 ≤ fan.offset (slit + i) x ∧ fan.offset (slit + i) x ≤ fan.sectorAngle (slit + i) ∧
      net.place i x = dist (pole : Space) x •
        direction (fan.openingAngle slit i.castSucc + fan.offset (slit + i) x) := by
  have poleF := fan.pole_mem_face (slit + i)
  have leftF := fan.left_mem_face (slit + i)
  have xF : x ∈ (fan.face (slit + i)).val := by rwa [← fan.triangle_eq_face]
  have radius : dist 0 (net.place i x) = dist (pole : Space) x := by
    rw [← net.at_pole i]
    exact net.rigid i _ poleF x xF
  have positive : 0 < dist 0 (net.place i x) := radius ▸ dist_pos.mpr nonpole.symm
  have nonzero : net.place i x ≠ 0 := (dist_pos.mp positive).symm
  have placed : net.place i x ∈ fan.openingTriangle slit i := by
    rw [← net.placed_triangle i]
    exact ⟨x, member, rfl⟩
  have width := fan.openingAngle_step slit i
  obtain ⟨θ, lower, upper, expression⟩ := radial_triangle_polar_representation _ _ _ _
    (fan.opening_radius_pos slit i.castSucc) (fan.opening_radius_pos slit i.succ)
    (by linarith [fan.sectorAngle_pos (slit + i)])
    (by linarith [fan.sectorAngle_lt_pi (slit + i)]) (net.place i x) nonzero placed
  have measured := triangle_angle_of_distances pole
    (fan.neighbor (slit + i)) x (net.place i pole)
    (net.place i (fan.neighbor (slit + i))) (net.place i x)
    (net.rigid i _ poleF _ leftF) (net.rigid i _ poleF x xF) (net.rigid i _ leftF x xF)
  rw [net.at_pole, net.at_left, expression] at measured
  change EuclideanGeometry.angle (_ • direction _) 0 (_ • direction _) = fan.offset (slit + i) x at measured
  rw [radial_angle _ _ _ _ (fan.opening_radius_pos slit i.castSucc) positive
    (sub_nonneg.mpr lower) (by linarith [fan.sectorAngle_lt_pi (slit + i)])] at measured
  refine ⟨by linarith, by linarith, ?_⟩
  rw [expression, radius, ← measured]
  congr 2
  ring

end Development
end SixVertexUnfolding.ConvexPolyhedron.FiveFaceFan
