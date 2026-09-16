import SixVertexUnfolding.Geometry.OctahedralFanCircle
import SixVertexUnfolding.Geometry.OctahedralFanNeighborhood

/-! Every angular coordinate occurs on every sufficiently small actual
vertex link, with the prescribed spatial radius. -/

namespace SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph

open Set OctahedralTriangles Real

variable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)
    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include small_faces in
/-- Small spheres cut out a complete circle of actual cone directions. -/
theorem fanCircleMap_small_link_surjective (pole : Fin 6) :
    ∃ ε > 0, ∀ ρ ∈ Ioo (0 : ℝ) ε, ∀ z : AddCircle (graph.totalAngleAt pole),
      ∃ x : frontier P.body, (x : Space) ∈ graph.fanCircleDomain pole ∧
        dist (x : Space) (graph.vertex pole) = ρ ∧ graph.fanCircleMap pole x = z := by
  letI : Fact (0 < graph.totalAngleAt pole) := ⟨graph.totalAngleAt_pos pole⟩
  let fan := Classical.choice (graph.exists_fan_development small_faces pole 0)
  obtain ⟨ε, positive, small_rays⟩ := graph.openingTriangles_small_rays pole 0
  refine ⟨ε, positive, ?_⟩
  intro ρ hr z
  obtain ⟨θ, hθ, same_z⟩ := AddCircle.eq_coe_Ico z
  obtain ⟨i, hi⟩ := mem_iUnion.mp (small_rays ρ ⟨hr.1.le, hr.2.le⟩ θ ⟨hθ.1, hθ.2.le⟩)
  rw [← fan.placed_triangle i] at hi
  obtain ⟨x, triangle, placed⟩ := hi
  simp only [zero_add] at triangle
  let F := graph.triangleFace small_faces (fanTriangle pole i)
  have xF : x ∈ F.val := graph.triangle_subset_face small_faces _ triangle
  have poleF : (graph.vertex pole : Space) ∈ F.val := graph.fan_sector_on_face pole small_faces i _ (by simp)
  have radius : dist (graph.vertex pole : Space) x = ρ := by
    calc
      dist (graph.vertex pole : Space) x = dist (fan.place i (graph.vertex pole)) (fan.place i x) :=
        (fan.rigid i _ (by simpa only [zero_add] using poleF) x (by simpa only [zero_add] using xF)).symm
      _ = dist 0 (ρ • direction θ) := by rw [fan.at_pole, placed]
      _ = ρ := polar_radius ρ θ hr.1.le
  have nonpole : x ≠ graph.vertex pole := by
    intro equal
    rw [equal, dist_self] at radius
    exact (ne_of_gt hr.1) radius.symm
  have coords := fan.point_polar_coordinates i x (by simpa only [zero_add] using triangle) nonpole
  simp only [zero_add] at coords
  have angle_lower : 0 ≤ graph.openingAngle pole 0 i.castSucc := by
    simpa only [openingAngle, Matrix.cons_val_zero] using
      (graph.openingAngle_strictMono pole 0).monotone (Fin.zero_le i.castSucc)
  have angle_upper : graph.openingAngle pole 0 i.succ ≤ graph.totalAngleAt pole := by
    rw [← graph.openingAngle_last pole 0]
    exact (graph.openingAngle_strictMono pole 0).monotone (Fin.le_last _)
  have step := graph.openingAngle_step pole 0 i
  simp only [zero_add] at step
  have total_lt := graph.totalAngleAt_lt_two_pi small_faces pole
  have measured : graph.openingAngle pole 0 i.castSucc + graph.fanOffset pole i x = θ := by
    apply polar_angle_eq_of_one_turn ρ ρ _ θ hr.1 hr.1
    · linarith [coords.2.1, hθ.1]
    · linarith [coords.1, hθ.2]
    · rw [← radius, ← coords.2.2]
      simpa only [radius] using placed
  refine ⟨⟨x, F.subset_frontier xF⟩, ⟨mem_iUnion.mpr ⟨i, triangle⟩, nonpole⟩,
    by simpa only [dist_comm] using radius, ?_⟩
  rw [graph.fanCircleMap_on_sector small_faces pole i x triangle nonpole]
  change ((graph.openingAngle pole 0 i.castSucc + graph.fanOffset pole i x : ℝ) :
    AddCircle (graph.totalAngleAt pole)) = z
  rw [measured, same_z]

end SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph
