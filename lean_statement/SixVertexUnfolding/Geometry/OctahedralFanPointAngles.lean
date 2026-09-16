import SixVertexUnfolding.Geometry.OctahedralFanDevelopment
import SixVertexUnfolding.Geometry.OctahedralFanHinges
import SixVertexUnfolding.Geometry.RadialTriangleCorners
import SixVertexUnfolding.Geometry.TriangleAngles

/-! The direction of a point within a fan triangle is its ordinary spatial
angle from that triangle's first radial edge. It is independent of the slit. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set OctahedralTriangles Real

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)

/-- The ordinary angle from the first edge of a vertex sector to a point in it. -/
noncomputable def fanOffset (pole : Fin 6) (sector : Fin 4) (x : Space) : ℝ :=
  EuclideanGeometry.angle (graph.vertex (fanNeighbor pole sector) : Space) (graph.vertex pole) x

namespace FanDevelopment

variable {graph} {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
    (F.val ∩ (P.vertices : Set Space)).ncard = 4}
  {pole : Fin 6} {slit : Fin 4} (fan : graph.FanDevelopment small_faces pole slit)

/-- A point's polar coordinates use its actual distance and actual angle at the vertex. -/
theorem point_polar_coordinates (i : Fin 4) (x : Space)
    (member : x ∈ graph.triangle (fanTriangle pole (slit + i)))
    (nonpole : x ≠ graph.vertex pole) :
    0 ≤ graph.fanOffset pole (slit + i) x ∧
      graph.fanOffset pole (slit + i) x ≤ graph.fanAngle pole (slit + i) ∧
      fan.place i x = dist (graph.vertex pole : Space) x •
        direction (graph.openingAngle pole slit i.castSucc + graph.fanOffset pole (slit + i) x) := by
  let F := graph.triangleFace small_faces (fanTriangle pole (slit + i))
  have poleF : (graph.vertex pole : Space) ∈ F.val :=
    graph.fan_sector_on_face pole small_faces (slit + i) _ (by simp)
  have leftF : (graph.vertex (fanNeighbor pole (slit + i)) : Space) ∈ F.val :=
    graph.fan_sector_on_face pole small_faces (slit + i) _ (by simp)
  have xF : x ∈ F.val := graph.triangle_subset_face small_faces _ member
  have radius : dist 0 (fan.place i x) = dist (graph.vertex pole : Space) x := by
    rw [← fan.at_pole i]
    exact fan.rigid i _ poleF x xF
  have positive : 0 < dist 0 (fan.place i x) := radius ▸ dist_pos.mpr nonpole.symm
  have nonzero : fan.place i x ≠ 0 := (dist_pos.mp positive).symm
  have placed : fan.place i x ∈ graph.openingTriangle pole slit i := by
    rw [← fan.placed_triangle i]
    exact ⟨x, member, rfl⟩
  have width := graph.openingAngle_step pole slit i
  obtain ⟨θ, lower, upper, expression⟩ := radial_triangle_polar_representation _ _ _ _
    (graph.opening_radius_pos pole slit i.castSucc) (graph.opening_radius_pos pole slit i.succ)
    (by linarith [graph.fanAngle_pos pole (slit + i)])
    (by linarith [graph.fanAngle_lt_pi pole (slit + i)]) (fan.place i x) nonzero placed
  have measured := triangle_angle_of_distances (graph.vertex pole)
    (graph.vertex (fanNeighbor pole (slit + i))) x (fan.place i (graph.vertex pole))
    (fan.place i (graph.vertex (fanNeighbor pole (slit + i)))) (fan.place i x)
    (fan.rigid i _ poleF _ leftF) (fan.rigid i _ poleF x xF) (fan.rigid i _ leftF x xF)
  rw [fan.at_pole, fan.at_left, expression] at measured
  change EuclideanGeometry.angle (_ • direction _) 0 (_ • direction _) =
    graph.fanOffset pole (slit + i) x at measured
  rw [radial_angle _ _ _ _ (graph.opening_radius_pos pole slit i.castSucc) positive
    (sub_nonneg.mpr lower) (by linarith [graph.fanAngle_lt_pi pole (slit + i)])] at measured
  refine ⟨by linarith, by linarith, ?_⟩
  rw [expression, radius, ← measured]
  congr 2
  ring

end FanDevelopment
end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
