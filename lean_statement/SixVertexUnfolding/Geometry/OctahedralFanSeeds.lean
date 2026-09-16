import SixVertexUnfolding.Geometry.OctahedralPocketCertificate
import SixVertexUnfolding.Geometry.RadialInterior

/-! Explicit rays through the interiors of the actual fan triangles. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development

open Real OctahedralTriangles

variable {P : ConvexPolyhedron} {graph : P.SixVertexGraph}
variable {small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
  (F.val ∩ (P.vertices : Set Space)).ncard = 4} {source : Fin 6} {slit : Fin 4}
variable (net : graph.Development small_faces source slit)

/-- The midpoint direction enters the finite fan face at every sufficiently small positive radius. -/
theorem small_midpoint_ray_in_fan (i : Fin 4) :
    ∃ ε > 0, ∀ r : ℝ, 0 < r → r < ε →
      r • direction ((graph.openingAngle (opposite source) slit i.castSucc +
        graph.openingAngle (opposite source) slit i.succ) / 2) ∈ interior (net.placedTriangle (false, i)) := by
  have step := graph.openingAngle_step (opposite source) slit i
  have positive := graph.fanAngle_pos (opposite source) (slit + i)
  have small := graph.fanAngle_lt_pi (opposite source) (slit + i)
  simp_rw [net.fan_placedTriangle]
  apply small_polar_ray_in_radial_triangle _ _ _ _ _ (graph.opening_radius_pos _ _ _) (graph.opening_radius_pos _ _ _)
  · linarith
  · linarith
  · linarith

include small_faces in
/-- The five actual radial directions strictly increase and leave a positive slit gap. -/
theorem opening_angles_ordered :
    let θ := graph.openingAngle (opposite source) slit
    θ 0 < θ 1 ∧ θ 1 < θ 2 ∧ θ 2 < θ 3 ∧ θ 3 < θ 4 ∧ θ 4 < θ 0 + 2 * π := by
  have mono := graph.openingAngle_strictMono (opposite source) slit
  refine ⟨mono (by decide), mono (by decide), mono (by decide), mono (by decide), ?_⟩
  have total := graph.totalAngleAt_lt_two_pi small_faces (opposite source)
  rw [← graph.openingAngle_last (opposite source) slit] at total
  simpa only [show graph.openingAngle (opposite source) slit 0 = 0 from rfl, zero_add] using total

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.Development
