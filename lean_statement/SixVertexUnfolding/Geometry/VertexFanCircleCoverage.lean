import SixVertexUnfolding.Geometry.VertexFanCircle
import SixVertexUnfolding.Geometry.VertexFanNeighborhood

/-! Every angular coordinate occurs on every sufficiently small actual
vertex link, with the prescribed spatial radius. -/

namespace SixVertexUnfolding.ConvexPolyhedron.VertexFaceFan

open Set Real

variable {P : ConvexPolyhedron} {pole : P.Vertex} {n : ℕ} [NeZero n]
  (fan : P.VertexFaceFan pole n) (size : P.vertices.card ≤ 6)
    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨
      (F.val ∩ (P.vertices : Set Space)).ncard = 4)

include size small_faces in
/-- Small spheres cut out a complete circle of actual cone directions. -/
theorem fanCircleMap_small_link_surjective :
    ∃ ε > 0, ∀ ρ ∈ Ioo (0 : ℝ) ε, ∀ z : AddCircle (fan.totalAngle),
      ∃ x : frontier P.body, (x : Space) ∈ fan.fanCircleDomain ∧
        dist (x : Space) (pole) = ρ ∧ fan.fanCircleMap x = z := by
  letI : Fact (0 < fan.totalAngle) := ⟨fan.totalAngle_pos⟩
  let net := Classical.choice (fan.exists_development 0)
  obtain ⟨ε, positive, small_rays⟩ := fan.openingTriangles_small_rays 0
  refine ⟨ε, positive, ?_⟩
  intro ρ hr z
  obtain ⟨θ, hθ, same_z⟩ := AddCircle.eq_coe_Ico z
  obtain ⟨i, hi⟩ := mem_iUnion.mp (small_rays ρ ⟨hr.1.le, hr.2.le⟩ θ ⟨hθ.1, hθ.2.le⟩)
  rw [← net.placed_triangle i] at hi
  obtain ⟨x, triangle, placed⟩ := hi
  simp only [zero_add] at triangle
  let F := fan.face i
  have xF : x ∈ F.val := fan.triangle_subset_face _ triangle
  have poleF : (pole : Space) ∈ F.val := fan.pole_mem i
  have radius : dist (pole : Space) x = ρ := by
    calc
      dist (pole : Space) x = dist (net.place i (pole)) (net.place i x) :=
        (net.rigid i _ (by simpa only [zero_add] using poleF) x (by simpa only [zero_add] using xF)).symm
      _ = dist 0 (ρ • direction θ) := by rw [net.at_pole, placed]
      _ = ρ := polar_radius ρ θ hr.1.le
  have nonpole : x ≠ pole := by
    intro equal
    rw [equal, dist_self] at radius
    exact (ne_of_gt hr.1) radius.symm
  have coords := net.point_polar_coordinates i x (by simpa only [zero_add] using triangle) nonpole
  simp only [zero_add] at coords
  have angle_lower : 0 ≤ fan.openingAngle 0 i.castSucc := by
    simpa only [Fin.castSucc_zero, fan.openingAngle_zero] using
      (fan.openingAngle_strictMono 0).monotone (Fin.zero_le i.castSucc)
  have angle_upper : fan.openingAngle 0 i.succ ≤ fan.totalAngle := by
    rw [← fan.openingAngle_last 0]
    exact (fan.openingAngle_strictMono 0).monotone (Fin.le_last _)
  have step := fan.openingAngle_step 0 i
  simp only [zero_add] at step
  have total_lt := fan.totalAngle_lt_two_pi size small_faces
  have measured : fan.openingAngle 0 i.castSucc + fan.offset i x = θ := by
    apply polar_angle_eq_of_one_turn ρ ρ _ θ hr.1 hr.1
    · linarith [coords.2.1, hθ.1]
    · linarith [coords.1, hθ.2]
    · rw [← radius, ← coords.2.2]
      simpa only [radius] using placed
  refine ⟨⟨x, F.subset_frontier xF⟩, ⟨mem_iUnion.mpr ⟨i, triangle⟩, nonpole⟩,
    by simpa only [dist_comm] using radius, ?_⟩
  rw [fan.fanCircleMap_on_sector small_faces i x triangle nonpole]
  change ((fan.openingAngle 0 i.castSucc + fan.offset i x : ℝ) :
    AddCircle (fan.totalAngle)) = z
  rw [measured, same_z]

end SixVertexUnfolding.ConvexPolyhedron.VertexFaceFan
